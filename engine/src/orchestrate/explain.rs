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
//! A completed pass is subset-minimal with respect to the source axiom
//! occurrences.  If the caller's check budget stops the pass, the current set
//! is still a valid (revalidated) justification, but is explicitly marked as
//! not subset-minimal.  This is the same black-box minimisation pattern used by
//! OWL explanation tooling, with deliberately small default bounds because one
//! explanation can require one complete classification per source axiom.

use std::path::Path;

use serde::Serialize;

use super::tmpfile::TempPath;
use super::{Classification, Config, OrchestrateError};
use crate::frontend::sexpr::{Node, Parser};
use crate::routing::Route;

pub const DEFAULT_MAX_AXIOMS: usize = 256;
pub const DEFAULT_MAX_SOURCE_BYTES: u64 = 8 * 1024 * 1024;

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
    fn entailed_by(&self, classification: &Classification) -> bool {
        if !classification.consistent {
            // Classical OWL semantics: an inconsistent ontology entails every
            // axiom and makes every class unsatisfiable.
            return true;
        }
        match self {
            Query::Inconsistent => false,
            Query::Unsatisfiable { class_iri } => {
                is_bottom(class_iri)
                    || classification
                        .unsatisfiable
                        .iter()
                        .any(|candidate| same_iri(candidate, class_iri))
            }
            Query::SubClass {
                sub_class,
                super_class,
            } => {
                same_iri(sub_class, super_class)
                    || is_bottom(sub_class)
                    || is_top(super_class)
                    || classification
                        .unsatisfiable
                        .iter()
                        .any(|candidate| same_iri(candidate, sub_class))
                    || classification.subsumptions.iter().any(|pair| {
                        same_iri(&pair[0], sub_class) && same_iri(&pair[1], super_class)
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

fn same_iri(left: &str, right: &str) -> bool {
    unbracketed(left) == unbracketed(right)
}

fn is_top(iri: &str) -> bool {
    matches!(
        unbracketed(iri),
        "owl:Thing" | "http://www.w3.org/2002/07/owl#Thing"
    )
}

fn is_bottom(iri: &str) -> bool {
    matches!(
        unbracketed(iri),
        "owl:Nothing" | "http://www.w3.org/2002/07/owl#Nothing" | "⊥"
    )
}

#[derive(Clone, Debug)]
pub struct Options {
    pub max_axioms: usize,
    /// Includes the initial full-source entailment check.
    pub max_checks: usize,
    pub max_source_bytes: u64,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            max_axioms: DEFAULT_MAX_AXIOMS,
            max_checks: DEFAULT_MAX_AXIOMS + 1,
            max_source_bytes: DEFAULT_MAX_SOURCE_BYTES,
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
    #[serde(rename = "oracleSubsetMinimal")]
    pub oracle_subset_minimal: bool,
    #[serde(rename = "limitReached")]
    pub limit_reached: bool,
    pub justifications: Vec<Justification>,
    pub notes: Vec<&'static str>,
}

#[derive(Debug)]
pub enum ExplainError {
    Io(std::io::Error),
    Parse(String),
    Limit(String),
    UnsafeRoute(String),
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

struct Minimized {
    entailed: bool,
    active: Vec<bool>,
    checks: usize,
    limit_reached: bool,
}

/// Greedy deletion is one-pass subset minimisation because OWL entailment is
/// monotone: if removing axiom `a` from a superset loses the entailment, no
/// later subset without `a` can regain it merely by deleting more axioms.
fn minimize<F, E>(axiom_count: usize, max_checks: usize, mut oracle: F) -> Result<Minimized, E>
where
    F: FnMut(&[bool]) -> Result<bool, E>,
{
    let mut active = vec![true; axiom_count];
    let mut checks = 1usize;
    if !oracle(&active)? {
        return Ok(Minimized {
            entailed: false,
            active,
            checks,
            limit_reached: false,
        });
    }
    let mut limit_reached = false;
    for index in 0..axiom_count {
        if checks >= max_checks {
            limit_reached = true;
            break;
        }
        active[index] = false;
        checks += 1;
        if !oracle(&active)? {
            active[index] = true;
        }
    }
    Ok(Minimized {
        entailed: true,
        active,
        checks,
        limit_reached,
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

    let candidate = TempPath::new(".explain.ofn");
    let minimized = minimize(
        document.axioms.len(),
        options.max_checks,
        |active| -> Result<bool, ExplainError> {
            std::fs::write(candidate.path(), document.render(active))?;
            let classification = super::classify(cfg, candidate.path())?;
            Ok(query.entailed_by(&classification))
        },
    )?;

    let notes = vec![
        "The justification is validated by KM's classification oracle, not by an independent proof checker.",
        "Subset minimality is relative to source axiom occurrences and KM's automatic production policy.",
        "Only self-contained OWL functional syntax and named-class subclass, unsatisfiability, or inconsistency queries are supported.",
    ];
    let (status, justifications) = if minimized.entailed {
        let axioms: Vec<SourceAxiom> = minimized
            .active
            .iter()
            .zip(&document.axioms)
            .filter_map(|(active, axiom)| active.then_some(axiom.clone()))
            .collect();
        (
            Status::Entailed,
            vec![Justification {
                axiom_count: axioms.len(),
                axioms,
            }],
        )
    } else {
        (Status::NotEntailed, Vec::new())
    };

    Ok(Report {
        schema_version: 1,
        status,
        query,
        method: "black-box-source-axiom-deletion",
        requested_route: requested_route.as_str().to_string(),
        reasoner_version: env!("CARGO_PKG_VERSION"),
        source_axiom_count: document.axioms.len(),
        classification_checks: minimized.checks,
        oracle_subset_minimal: minimized.entailed && !minimized.limit_reached,
        limit_reached: minimized.limit_reached,
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
    fn deletion_returns_one_subset_minimal_support() {
        // Query follows from (0 and 1); axiom 2 is noise.  The monotone oracle
        // models an entailment check without running a reasoner in this unit.
        let result = minimize(3, 4, |active| -> Result<bool, ()> {
            Ok(active[0] && active[1])
        })
        .unwrap();
        assert!(result.entailed);
        assert_eq!(result.active, vec![true, true, false]);
        assert_eq!(result.checks, 4);
        assert!(!result.limit_reached);
    }

    #[test]
    fn budgeted_result_stays_entailed_but_is_not_minimal() {
        let result = minimize(3, 1, |_active| -> Result<bool, ()> { Ok(true) }).unwrap();
        assert!(result.entailed);
        assert_eq!(result.active, vec![true, true, true]);
        assert_eq!(result.checks, 1);
        assert!(result.limit_reached);
    }

    #[test]
    fn query_recognises_taxonomy_unsat_and_owl_tautologies() {
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
        .entailed_by(&classification));
        assert!(Query::SubClass {
            sub_class: "http://e/U".into(),
            super_class: "http://e/Anything".into(),
        }
        .entailed_by(&classification));
        assert!(Query::Unsatisfiable {
            class_iri: "http://e/U".into(),
        }
        .entailed_by(&classification));
        assert!(Query::SubClass {
            sub_class: "http://e/Fresh".into(),
            super_class: "owl:Thing".into(),
        }
        .entailed_by(&classification));
        assert!(!Query::Inconsistent.entailed_by(&classification));
    }

    #[test]
    fn inconsistent_ontology_entails_every_supported_query() {
        let classification = Classification {
            consistent: false,
            subsumptions: Vec::new(),
            unsatisfiable: Vec::new(),
            dropped: 0,
        };
        assert!(Query::Inconsistent.entailed_by(&classification));
        assert!(Query::SubClass {
            sub_class: "http://e/A".into(),
            super_class: "http://e/B".into(),
        }
        .entailed_by(&classification));
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
