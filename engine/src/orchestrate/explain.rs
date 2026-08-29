//! Bounded source-axiom justifications for named-class entailments.
//!
//! This module deliberately does not instrument the saturation engines.  An
//! explanation request is an opt-in, black-box deletion pass over the original
//! OWL functional-syntax axioms: classify the full source, remove one source
//! axiom, and keep the removal only when KM still entails the query.  Every
//! returned set is therefore revalidated by the automatic production
//! classifier. Forced matrix and manual routes are rejected because they
//! bypass the source-profile semantic-fragment gate.
//!
//! Each returned support is subset-minimal with respect to source axiom
//! occurrences and is reclassified once after minimization. A hitting-set tree
//! enumerates alternatives. If a check budget stops a branch, that unfinished
//! support is discarded; already verified justifications remain explicitly
//! marked as a bounded, incomplete enumeration. This is the same black-box
//! minimisation pattern used by OWL explanation tooling, with deliberately
//! small default bounds because one explanation can require one complete
//! classification per source axiom.

use std::borrow::Cow;
use std::collections::{HashMap, HashSet, VecDeque};
use std::path::Path;

use serde::Serialize;

use super::tmpfile::TempPath;
use super::{Classification, Config, OrchestrateError};
use crate::frontend::sexpr::{Node, Parser};
use crate::routing::Route;

pub const DEFAULT_MAX_AXIOMS: usize = 256;
pub const DEFAULT_MAX_SOURCE_BYTES: u64 = 8 * 1024 * 1024;
pub const DEFAULT_MAX_JUSTIFICATIONS: usize = 1;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case")]
pub enum Query {
    SubClass {
        #[serde(rename = "subClass")]
        sub_class: String,
        #[serde(rename = "superClass")]
        super_class: String,
    },
    Unsatisfiable {
        #[serde(rename = "class")]
        class_iri: String,
    },
    Inconsistent,
}

impl Query {
    fn entailed_by(&self, classification: &Classification, iris: &IriResolver) -> bool {
        if !classification.consistent {
            // Classical OWL semantics: an inconsistent ontology entails every
            // axiom and makes every class unsatisfiable.
            return true;
        }
        match self {
            Query::Inconsistent => false,
            Query::Unsatisfiable { class_iri } => {
                is_bottom(class_iri, iris)
                    || classification
                        .unsatisfiable
                        .iter()
                        .any(|candidate| same_iri(candidate, class_iri, iris))
            }
            Query::SubClass {
                sub_class,
                super_class,
            } => {
                same_iri(sub_class, super_class, iris)
                    || is_bottom(sub_class, iris)
                    || is_top(super_class, iris)
                    || classification
                        .unsatisfiable
                        .iter()
                        .any(|candidate| same_iri(candidate, sub_class, iris))
                    || classification.subsumptions.iter().any(|pair| {
                        same_iri(&pair[0], sub_class, iris) && same_iri(&pair[1], super_class, iris)
                    })
            }
        }
    }
}

fn unbracketed(iri: &str) -> &str {
    let iri = iri.trim();
    iri.strip_prefix('<')
        .and_then(|value| value.strip_suffix('>'))
        .unwrap_or(iri)
}

#[derive(Default)]
struct IriResolver {
    prefixes: HashMap<String, String>,
}

impl IriResolver {
    fn from_preamble(items: &[String]) -> Self {
        let mut prefixes = HashMap::new();
        for item in items {
            let Some(body) = item
                .strip_prefix("Prefix(")
                .and_then(|body| body.strip_suffix(')'))
            else {
                continue;
            };
            let Some((prefix, iri)) = body.split_once("=<") else {
                continue;
            };
            if let Some(base) = iri.strip_suffix('>') {
                prefixes.insert(prefix.to_string(), base.to_string());
            }
        }
        IriResolver { prefixes }
    }

    fn resolve<'a>(&self, iri: &'a str) -> Cow<'a, str> {
        let iri = unbracketed(iri);
        if let Some(colon) = iri.find(':') {
            let (prefix, local) = iri.split_at(colon + 1);
            if let Some(base) = self.prefixes.get(prefix) {
                return Cow::Owned(format!("{base}{local}"));
            }
        }
        Cow::Borrowed(iri)
    }
}

fn same_iri(left: &str, right: &str, iris: &IriResolver) -> bool {
    iris.resolve(left) == iris.resolve(right)
}

fn is_top(iri: &str, iris: &IriResolver) -> bool {
    matches!(
        iris.resolve(iri).as_ref(),
        "owl:Thing" | "http://www.w3.org/2002/07/owl#Thing"
    )
}

fn is_bottom(iri: &str, iris: &IriResolver) -> bool {
    matches!(
        iris.resolve(iri).as_ref(),
        "owl:Nothing" | "http://www.w3.org/2002/07/owl#Nothing" | "⊥"
    )
}

#[derive(Clone, Debug)]
pub struct Options {
    pub max_axioms: usize,
    /// Includes the initial full-source entailment check.
    pub max_checks: usize,
    pub max_source_bytes: u64,
    pub max_justifications: usize,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_axioms: DEFAULT_MAX_AXIOMS,
            // One full-source check, one deletion check per source axiom, and
            // one independent verification of the minimized support.
            max_checks: DEFAULT_MAX_AXIOMS + 2,
            max_source_bytes: DEFAULT_MAX_SOURCE_BYTES,
            max_justifications: DEFAULT_MAX_JUSTIFICATIONS,
        }
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct SourceAxiom {
    /// Stable within one source document: the one-based ontology-child order.
    pub id: String,
    pub ordinal: usize,
    #[serde(rename = "functionalSyntax")]
    pub functional_syntax: String,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Status {
    Entailed,
    NotEntailed,
}

#[derive(Debug, Serialize)]
pub struct Justification {
    #[serde(rename = "axiomCount")]
    pub axiom_count: usize,
    pub verified: bool,
    #[serde(rename = "subsetMinimal")]
    pub subset_minimal: bool,
    pub axioms: Vec<SourceAxiom>,
}

/// Stable, dependency-free protocol for CLI, OWLAPI, and Protégé callers.
#[derive(Debug, Serialize)]
pub struct Report {
    #[serde(rename = "schemaVersion")]
    pub schema_version: u32,
    pub status: Status,
    pub query: Query,
    pub method: &'static str,
    #[serde(rename = "requestedRoute")]
    pub requested_route: String,
    #[serde(rename = "reasonerVersion")]
    pub reasoner_version: &'static str,
    #[serde(rename = "sourceAxiomCount")]
    pub source_axiom_count: usize,
    #[serde(rename = "classificationChecks")]
    pub classification_checks: usize,
    #[serde(rename = "classificationCheckLimit")]
    pub classification_check_limit: usize,
    #[serde(rename = "justificationLimit")]
    pub justification_limit: usize,
    #[serde(rename = "oracleSubsetMinimal")]
    pub oracle_subset_minimal: bool,
    #[serde(rename = "enumerationComplete")]
    pub enumeration_complete: bool,
    #[serde(rename = "limitReached")]
    pub limit_reached: bool,
    #[serde(rename = "checkLimitReached")]
    pub check_limit_reached: bool,
    #[serde(rename = "justificationLimitReached")]
    pub justification_limit_reached: bool,
    #[serde(rename = "prefixDeclarations")]
    pub prefix_declarations: Vec<String>,
    pub justifications: Vec<Justification>,
    pub notes: Vec<&'static str>,
}

#[derive(Debug)]
pub enum ExplainError {
    Io(std::io::Error),
    Parse(String),
    Limit(String),
    UnsafeRoute(String),
    Verification(String),
    Classify(OrchestrateError),
}

impl std::fmt::Display for ExplainError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExplainError::Io(error) => write!(f, "io: {error}"),
            ExplainError::Parse(error) => write!(f, "functional-syntax parse: {error}"),
            ExplainError::Limit(error) => write!(f, "explanation limit: {error}"),
            ExplainError::UnsafeRoute(route) => write!(
                f,
                "route {route:?} is not an explanation-safe production oracle; use auto"
            ),
            ExplainError::Verification(error) => {
                write!(f, "explanation verification: {error}")
            }
            ExplainError::Classify(error) => write!(f, "classification oracle: {error}"),
        }
    }
}

impl std::error::Error for ExplainError {}

impl From<std::io::Error> for ExplainError {
    fn from(error: std::io::Error) -> Self {
        ExplainError::Io(error)
    }
}

impl From<OrchestrateError> for ExplainError {
    fn from(error: OrchestrateError) -> Self {
        ExplainError::Classify(error)
    }
}

struct SourceDocument {
    top_level: Vec<String>,
    ontology_metadata: Vec<String>,
    axioms: Vec<SourceAxiom>,
}

impl SourceDocument {
    fn parse(text: &str, max_axioms: usize) -> Result<Self, ExplainError> {
        // Count with the existing streaming parser before materialising the
        // small, explanation-only source AST.  Two bare ontology IRI/version
        // tokens are metadata rather than candidate axioms.
        let mut children = 0usize;
        crate::frontend::parse::for_each_ontology_child(text, |_| {
            children = children.saturating_add(1);
            Ok(())
        })
        .map_err(|error| ExplainError::Parse(error.0))?;
        if children > max_axioms.saturating_add(2) {
            return Err(ExplainError::Limit(format!(
                "ontology has at least {} children; --max-axioms is {}",
                children.saturating_sub(2),
                max_axioms
            )));
        }

        let mut parser = Parser::new(text);
        let mut top_level = Vec::new();
        let mut ontology_metadata = Vec::new();
        let mut axioms = Vec::new();
        let mut ontology_seen = false;
        while parser.peek().is_some() {
            let node = parser.parse().map_err(ExplainError::Parse)?;
            match node {
                Node::List("Ontology", args) => {
                    if ontology_seen {
                        return Err(ExplainError::Parse(
                            "multiple Ontology(...) forms are not supported".into(),
                        ));
                    }
                    ontology_seen = true;
                    for (child_index, child) in args.iter().enumerate() {
                        match child {
                            Node::Atom(_) => ontology_metadata.push(render_node(child)),
                            Node::List(_, _) => {
                                let ordinal = child_index + 1;
                                axioms.push(SourceAxiom {
                                    id: format!("ax{ordinal:06}"),
                                    ordinal,
                                    functional_syntax: render_node(child),
                                });
                            }
                        }
                    }
                }
                other => top_level.push(render_node(&other)),
            }
        }
        if !ontology_seen {
            return Err(ExplainError::Parse(
                "expected a self-contained Ontology(...) document".into(),
            ));
        }
        if axioms.len() > max_axioms {
            return Err(ExplainError::Limit(format!(
                "ontology has {} source axioms; --max-axioms is {}",
                axioms.len(),
                max_axioms
            )));
        }
        Ok(SourceDocument {
            top_level,
            ontology_metadata,
            axioms,
        })
    }

    fn render(&self, active: &[bool]) -> String {
        debug_assert_eq!(active.len(), self.axioms.len());
        let mut out = String::new();
        for item in &self.top_level {
            out.push_str(item);
            out.push('\n');
        }
        out.push_str("Ontology(\n");
        for item in &self.ontology_metadata {
            out.push_str("  ");
            out.push_str(item);
            out.push('\n');
        }
        for (keep, axiom) in active.iter().zip(&self.axioms) {
            if *keep {
                out.push_str("  ");
                out.push_str(&axiom.functional_syntax);
                out.push('\n');
            }
        }
        out.push_str(")\n");
        out
    }
}

/// Canonical functional-syntax spelling of one zero-copy parser node.  The
/// source ordinal and this spelling are sufficient for an OWLAPI caller to map
/// a returned explanation back to its flattened input ontology.
fn render_node(node: &Node<'_>) -> String {
    match node {
        Node::Atom(atom) => (*atom).to_string(),
        Node::List(head, args) => {
            let mut out = String::from(*head);
            out.push('(');
            let mut index = 0usize;
            let mut first = true;
            while index < args.len() {
                if !first {
                    out.push(' ');
                }
                first = false;
                if let Node::Atom(literal) = &args[index] {
                    if literal.starts_with('"') {
                        out.push_str(literal);
                        if let Some(Node::Atom(suffix)) = args.get(index + 1) {
                            if suffix.starts_with("^^") || suffix.starts_with('@') {
                                out.push_str(suffix);
                                index += 2;
                                continue;
                            }
                        }
                        index += 1;
                        continue;
                    }
                }
                out.push_str(&render_node(&args[index]));
                index += 1;
            }
            out.push(')');
            out
        }
    }
}

struct Enumeration {
    entailed: bool,
    justifications: Vec<Vec<bool>>,
    checks: usize,
    enumeration_complete: bool,
    check_limit_reached: bool,
    justification_limit_reached: bool,
}

fn checked<F>(
    active: &[bool],
    checks: &mut usize,
    max_checks: usize,
    oracle: &mut F,
) -> Result<Option<bool>, ExplainError>
where
    F: FnMut(&[bool]) -> Result<bool, ExplainError>,
{
    if *checks >= max_checks {
        return Ok(None);
    }
    *checks += 1;
    oracle(active).map(Some)
}

/// Minimise one known-entailing candidate under a monotone entailment oracle.
///
/// Small supports keep the simple deterministic one-axiom deletion order.
/// For a large source, delta debugging first removes entailing chunks and
/// increases the partition granularity only when no whole chunk is removable.
/// Reaching singleton chunks proves one-deletion minimality; monotonicity then
/// makes that subset-minimal.  Sparse justifications in large ontologies need
/// logarithmically many successful chunk removals instead of one complete
/// classification per source axiom.
fn minimise<F>(
    candidate: &[bool],
    checks: &mut usize,
    max_checks: usize,
    oracle: &mut F,
) -> Result<Option<Vec<bool>>, ExplainError>
where
    F: FnMut(&[bool]) -> Result<bool, ExplainError>,
{
    let mut active = candidate.to_vec();
    let active_count = active.iter().filter(|present| **present).count();
    if active_count <= 32 {
        for index in 0..active.len() {
            if !active[index] {
                continue;
            }
            active[index] = false;
            let Some(entailed) = checked(&active, checks, max_checks, oracle)? else {
                return Ok(None);
            };
            if !entailed {
                active[index] = true;
            }
        }
        return Ok(Some(active));
    }

    let mut granularity = 2usize;
    loop {
        let indices: Vec<usize> = active
            .iter()
            .enumerate()
            .filter_map(|(index, present)| present.then_some(index))
            .collect();
        if indices.is_empty() {
            return Ok(Some(active));
        }
        let chunk_size = indices.len().div_ceil(granularity);
        let mut removed_chunk = false;
        for chunk in indices.chunks(chunk_size) {
            let mut trial = active.clone();
            for index in chunk {
                trial[*index] = false;
            }
            let Some(entailed) = checked(&trial, checks, max_checks, oracle)? else {
                return Ok(None);
            };
            if entailed {
                active = trial;
                granularity = granularity.saturating_sub(1).max(2);
                removed_chunk = true;
                break;
            }
        }
        if removed_chunk {
            continue;
        }
        if granularity >= indices.len() {
            return Ok(Some(active));
        }
        granularity = (granularity * 2).min(indices.len());
    }
}

/// Enumerate subset-minimal supports with a deterministic hitting-set tree.
///
/// Each entailing branch is minimized by greedy deletion. Greedy deletion is
/// one-pass subset minimisation because OWL entailment is monotone: if removing
/// axiom `a` from a superset loses the entailment, no later subset without `a`
/// can regain it merely by deleting more axioms. To find alternatives, branch
/// from the pre-minimization candidate once for every axiom in the resulting
/// support. Every support is classified once more after minimization; a support
/// is never published when that verification or the minimization budget cannot
/// complete.
fn enumerate<F>(
    axiom_count: usize,
    max_checks: usize,
    max_justifications: usize,
    mut oracle: F,
) -> Result<Enumeration, ExplainError>
where
    F: FnMut(&[bool]) -> Result<bool, ExplainError>,
{
    let full = vec![true; axiom_count];
    let mut checks = 0usize;
    let initially_entailed = checked(&full, &mut checks, max_checks, &mut oracle)?
        .expect("max_checks is validated before enumeration");
    if !initially_entailed {
        return Ok(Enumeration {
            entailed: false,
            justifications: Vec::new(),
            checks,
            enumeration_complete: true,
            check_limit_reached: false,
            justification_limit_reached: false,
        });
    }

    let mut queue = VecDeque::from([(full.clone(), true)]);
    let mut seen_candidates = HashSet::from([full]);
    let mut seen_justifications = HashSet::new();
    let mut justifications = Vec::new();
    let mut check_limit_reached = false;
    let mut justification_limit_reached = false;

    'search: while let Some((candidate, known_entailed)) = queue.pop_front() {
        if justifications.len() >= max_justifications {
            justification_limit_reached = true;
            break;
        }
        if !known_entailed {
            let Some(entailed) = checked(&candidate, &mut checks, max_checks, &mut oracle)? else {
                check_limit_reached = true;
                break;
            };
            if !entailed {
                continue;
            }
        }

        let Some(active) = minimise(&candidate, &mut checks, max_checks, &mut oracle)? else {
            check_limit_reached = true;
            break 'search;
        };

        // Deliberately bypass any cached branch verdict. This exact final set
        // must be reclassified before it is exposed as a justification.
        let Some(verified) = checked(&active, &mut checks, max_checks, &mut oracle)? else {
            check_limit_reached = true;
            break;
        };
        if !verified {
            return Err(ExplainError::Verification(
                "the minimized source set did not reproduce its entailment".into(),
            ));
        }

        if seen_justifications.insert(active.clone()) {
            justifications.push(active.clone());
        }

        // A different minimal support must omit at least one axiom from this
        // support. Accumulated omissions in `candidate` form the hitting-set
        // tree path; duplicate candidates are discarded deterministically.
        for (index, present) in active.iter().enumerate() {
            if *present {
                let mut child = candidate.clone();
                child[index] = false;
                if seen_candidates.insert(child.clone()) {
                    queue.push_back((child, false));
                }
            }
        }
    }

    let enumeration_complete =
        queue.is_empty() && !check_limit_reached && !justification_limit_reached;
    Ok(Enumeration {
        entailed: true,
        justifications,
        checks,
        enumeration_complete,
        check_limit_reached,
        justification_limit_reached,
    })
}

pub fn explain(
    cfg: &Config,
    ontology: &Path,
    query: Query,
    options: &Options,
    requested_route: Route,
) -> Result<Report, ExplainError> {
    // Check before reading the source or creating any candidate. A library
    // caller must not be able to bypass the CLI's production-oracle boundary.
    if !requested_route.is_explanation_safe() {
        return Err(ExplainError::UnsafeRoute(
            requested_route.as_str().to_string(),
        ));
    }

    // Enforce the typed API contract too. A caller may have constructed `cfg`
    // while a manual or measurement route was ambient; each candidate must
    // nevertheless enter `classify` through the automatic semantic gate. The
    // guard restores the caller's process environment when extraction ends.
    let _environment_guard = crate::routing::EnvironmentGuard::capture();
    std::env::set_var("KM_ROUTE", Route::Auto.as_str());

    if options.max_axioms == 0 {
        return Err(ExplainError::Limit(
            "--max-axioms must be greater than zero".into(),
        ));
    }
    if options.max_checks == 0 {
        return Err(ExplainError::Limit(
            "--max-checks must be greater than zero".into(),
        ));
    }
    if options.max_justifications == 0 {
        return Err(ExplainError::Limit(
            "--max-justifications must be greater than zero".into(),
        ));
    }
    let source_size = std::fs::metadata(ontology)?.len();
    if source_size > options.max_source_bytes {
        return Err(ExplainError::Limit(format!(
            "source is {source_size} bytes; --max-source-bytes is {}",
            options.max_source_bytes
        )));
    }
    let source = std::fs::read_to_string(ontology)?;
    let document = SourceDocument::parse(&source, options.max_axioms)?;
    drop(source);
    let iri_resolver = IriResolver::from_preamble(&document.top_level);

    let candidate = TempPath::new(".explain.ofn");
    let enumeration = enumerate(
        document.axioms.len(),
        options.max_checks,
        options.max_justifications,
        |active| -> Result<bool, ExplainError> {
            std::fs::write(candidate.path(), document.render(active))?;
            let evidence = super::classify_with_evidence(cfg, candidate.path())?;
            let classification = evidence.classification;
            let consistency_only_certificate =
                matches!(query, Query::Inconsistent) && evidence.consistency_certified;
            if classification.dropped != 0 && !consistency_only_certificate {
                return Err(ExplainError::Classify(OrchestrateError::OutOfFragment(
                    format!(
                        "classification dropped {} clause(s) for an explanation candidate",
                        classification.dropped
                    ),
                )));
            }
            Ok(query.entailed_by(&classification, &iri_resolver))
        },
    )?;

    let notes = vec![
        "The justification is validated by KM's classification oracle, not by an independent proof checker.",
        "Every returned support was minimized and then reclassified as an exact source subset.",
        "Subset minimality and enumeration are relative to source axiom occurrences and KM's automatic production policy.",
        "Only self-contained OWL functional syntax and named-class subclass, unsatisfiability, or inconsistency queries are supported.",
    ];
    let (status, justifications) = if enumeration.entailed {
        (
            Status::Entailed,
            enumeration
                .justifications
                .iter()
                .map(|active| {
                    let axioms: Vec<SourceAxiom> = active
                        .iter()
                        .zip(&document.axioms)
                        .filter_map(|(active, axiom)| active.then_some(axiom.clone()))
                        .collect();
                    Justification {
                        axiom_count: axioms.len(),
                        verified: true,
                        subset_minimal: true,
                        axioms,
                    }
                })
                .collect(),
        )
    } else {
        (Status::NotEntailed, Vec::new())
    };
    let oracle_subset_minimal = !justifications.is_empty()
        && justifications
            .iter()
            .all(|justification| justification.verified && justification.subset_minimal);
    let limit_reached = enumeration.check_limit_reached || enumeration.justification_limit_reached;
    let prefix_declarations = document
        .top_level
        .iter()
        .filter(|item| item.starts_with("Prefix("))
        .cloned()
        .collect();

    Ok(Report {
        schema_version: 2,
        status,
        query,
        method: "black-box-hitting-set-source-axiom-deletion",
        requested_route: requested_route.as_str().to_string(),
        reasoner_version: env!("CARGO_PKG_VERSION"),
        source_axiom_count: document.axioms.len(),
        classification_checks: enumeration.checks,
        classification_check_limit: options.max_checks,
        justification_limit: options.max_justifications,
        oracle_subset_minimal,
        enumeration_complete: enumeration.enumeration_complete,
        limit_reached,
        check_limit_reached: enumeration.check_limit_reached,
        justification_limit_reached: enumeration.justification_limit_reached,
        prefix_declarations,
        justifications,
        notes,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_document_round_trip_keeps_axioms_and_literal_suffixes() {
        let text = r#"
Prefix(:=<http://example.org/>)
Ontology(<http://example.org/o>
  Declaration(Class(:A))
  DataPropertyAssertion(:p :a "5"^^<http://www.w3.org/2001/XMLSchema#integer>)
  SubClassOf(:A :B)
)
"#;
        let document = SourceDocument::parse(text, 8).expect("source parses");
        assert_eq!(document.axioms.len(), 3);
        let rendered = document.render(&[false, true, true]);
        assert!(!rendered.contains("Declaration"));
        assert!(rendered.contains("\"5\"^^<http://www.w3.org/2001/XMLSchema#integer>"));
        assert!(rendered.contains("SubClassOf(:A :B)"));
        SourceDocument::parse(&rendered, 8).expect("rendered subset parses");
    }

    #[test]
    fn deletion_returns_one_verified_subset_minimal_support() {
        // Query follows from (0 and 1); axiom 2 is noise.  The monotone oracle
        // models an entailment check without running a reasoner in this unit.
        let result = enumerate(3, 8, 1, |active| Ok(active[0] && active[1])).unwrap();
        assert!(result.entailed);
        assert_eq!(result.justifications, vec![vec![true, true, false]]);
        assert_eq!(result.checks, 5);
        assert!(!result.check_limit_reached);
        assert!(result.justification_limit_reached);
        assert!(!result.enumeration_complete);
    }

    #[test]
    fn hitting_set_tree_finds_two_distinct_minimal_supports() {
        let result = enumerate(5, 64, 2, |active| {
            Ok((active[0] && active[1]) || (active[2] && active[3]))
        })
        .unwrap();
        assert!(result.entailed);
        assert_eq!(result.justifications.len(), 2);
        assert!(result
            .justifications
            .contains(&vec![true, true, false, false, false]));
        assert!(result
            .justifications
            .contains(&vec![false, false, true, true, false]));
        assert!(result.justification_limit_reached);
        assert!(!result.enumeration_complete);
    }

    #[test]
    fn sparse_large_support_is_minimised_without_a_linear_oracle_budget() {
        let result = enumerate(4_096, 96, 1, |active| {
            Ok(active[17] && active[4_000])
        })
        .unwrap();
        assert!(result.entailed);
        assert_eq!(result.justifications.len(), 1);
        let support = &result.justifications[0];
        assert_eq!(support.iter().filter(|present| **present).count(), 2);
        assert!(support[17]);
        assert!(support[4_000]);
        assert!(result.checks < 80, "checks={}", result.checks);
        assert!(!result.check_limit_reached);
    }

    #[test]
    fn unfinished_minimization_is_not_returned_when_check_budget_ends() {
        let result = enumerate(3, 2, 1, |_active| Ok(true)).unwrap();
        assert!(result.entailed);
        assert!(result.justifications.is_empty());
        assert_eq!(result.checks, 2);
        assert!(result.check_limit_reached);
        assert!(!result.enumeration_complete);
    }

    #[test]
    fn tautology_has_one_verified_empty_justification() {
        let result = enumerate(2, 8, 1, |_active| Ok(true)).unwrap();
        assert!(result.entailed);
        assert_eq!(result.justifications, vec![vec![false, false]]);
        assert!(result.enumeration_complete);
        assert!(!result.check_limit_reached);
        assert!(!result.justification_limit_reached);
    }

    #[test]
    fn query_recognises_taxonomy_unsat_and_owl_tautologies() {
        let iris = IriResolver::default();
        let classification = Classification {
            consistent: true,
            subsumptions: vec![["http://e/A".into(), "http://e/B".into()]],
            unsatisfiable: vec!["http://e/U".into()],
            dropped: 0,
        };
        assert!(Query::SubClass {
            sub_class: "<http://e/A>".into(),
            super_class: "http://e/B".into(),
        }
        .entailed_by(&classification, &iris));
        assert!(Query::SubClass {
            sub_class: "http://e/U".into(),
            super_class: "http://e/Anything".into(),
        }
        .entailed_by(&classification, &iris));
        assert!(Query::Unsatisfiable {
            class_iri: "http://e/U".into(),
        }
        .entailed_by(&classification, &iris));
        assert!(Query::SubClass {
            sub_class: "http://e/Fresh".into(),
            super_class: "owl:Thing".into(),
        }
        .entailed_by(&classification, &iris));
        assert!(!Query::Inconsistent.entailed_by(&classification, &iris));
    }

    #[test]
    fn query_resolves_source_prefixes_without_local_name_matching() {
        let iris = IriResolver::from_preamble(&[
            "Prefix(:=<http://example.org/>)".into(),
            "Prefix(other:=<http://other.example/>)".into(),
        ]);
        let classification = Classification {
            consistent: true,
            subsumptions: vec![[":A".into(), ":B".into()]],
            unsatisfiable: Vec::new(),
            dropped: 0,
        };
        assert!(Query::SubClass {
            sub_class: "http://example.org/A".into(),
            super_class: "http://example.org/B".into(),
        }
        .entailed_by(&classification, &iris));
        assert!(!Query::SubClass {
            sub_class: "http://other.example/A".into(),
            super_class: "http://example.org/B".into(),
        }
        .entailed_by(&classification, &iris));
    }

    #[test]
    fn inconsistent_ontology_entails_every_supported_query() {
        let iris = IriResolver::default();
        let classification = Classification {
            consistent: false,
            subsumptions: Vec::new(),
            unsatisfiable: Vec::new(),
            dropped: 0,
        };
        assert!(Query::Inconsistent.entailed_by(&classification, &iris));
        assert!(Query::SubClass {
            sub_class: "http://e/A".into(),
            super_class: "http://e/B".into(),
        }
        .entailed_by(&classification, &iris));
    }

    #[test]
    fn api_rejects_a_forced_measurement_route_before_reading_source() {
        let config = Config::from_env();
        let error = explain(
            &config,
            Path::new("/path-is-never-read.ofn"),
            Query::Inconsistent,
            &Options::default(),
            Route::HtQo,
        )
        .unwrap_err();
        assert!(matches!(error, ExplainError::UnsafeRoute(route) if route == "ht_qo"));
    }
}
