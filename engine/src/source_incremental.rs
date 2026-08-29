//! Stateful incremental classification over complete OWL Functional Syntax.
//!
//! This is the source-level transport used by OWLAPI clients.  Unlike the
//! lower-level `incremental` command, every transaction re-runs the complete
//! frontend and therefore cannot silently lose RBox, cardinality, rule, ABox,
//! profile, or IRI-mapping side state.  Routes whose complete state is already
//! represented by normalized clauses reuse [`IncrementalClassifier`].  Other
//! routes take an explicit exact-rebuild fallback until their typed retained
//! adapters are connected to this same protocol.

use std::collections::{BTreeSet, HashMap, VecDeque};
use std::io::{BufRead, Write};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::frontend::FrontendResult;
use crate::incremental::{ChangeStrategy, ClauseId, IncrementalChange, IncrementalClassifier};
use crate::json_io::JClause;
use crate::orchestrate::{Classification, Config};

#[derive(Clone, Debug, Serialize)]
pub struct SourceIncrementalReceipt {
    pub revision: u64,
    pub route_before: String,
    pub route_after: String,
    pub route_migrated: bool,
    pub strategy: ChangeStrategy,
    pub reused_fixpoint: bool,
    pub reused_subsumptions: usize,
    pub reused_edges: usize,
    pub added_normalized_clauses: usize,
    pub removed_normalized_clauses: usize,
    /// `false` identifies an honest batch safety fallback, never hidden reuse.
    pub meaningful_incremental_update: bool,
}

enum SourceBackend {
    Incremental {
        classifier: IncrementalClassifier,
        clauses: Vec<JClause>,
        ids: Vec<ClauseId>,
    },
    ExactBatch,
}

pub struct SourceIncrementalClassifier {
    revision: u64,
    route: String,
    frontend: FrontendResult,
    classification: Classification,
    backend: SourceBackend,
}

impl SourceIncrementalClassifier {
    pub fn new(source: &str) -> Result<Self, String> {
        let frontend = normalize_automatic(source)?;
        let route = frontend.route.clone();
        if clause_state_is_complete(&frontend) {
            if let Ok(classifier) = with_route_environment(&route, || {
                IncrementalClassifier::new(frontend.clauses.clone())
            })? {
                let ids = classifier.clause_ids();
                let classification = map_incremental_result(&frontend, classifier.result());
                return Ok(Self {
                    revision: 0,
                    route,
                    frontend,
                    classification,
                    backend: SourceBackend::Incremental {
                        classifier,
                        clauses: Vec::new(), // filled below
                        ids,
                    },
                }
                .with_live_clauses());
            }
        }
        let classification = classify_source_exact(source)?;
        Ok(Self {
            revision: 0,
            route,
            frontend,
            classification,
            backend: SourceBackend::ExactBatch,
        })
    }

    fn with_live_clauses(mut self) -> Self {
        if let SourceBackend::Incremental { clauses, .. } = &mut self.backend {
            *clauses = self.frontend.clauses.clone();
        }
        self
    }

    /// Atomically replace the complete flattened source ontology.
    pub fn replace_source(&mut self, source: &str) -> Result<SourceIncrementalReceipt, String> {
        let candidate = normalize_automatic(source)?;
        let route_before = self.route.clone();
        let route_after = candidate.route.clone();

        if clause_state_is_complete(&candidate) {
            if let SourceBackend::Incremental {
                classifier,
                clauses,
                ids,
            } = &mut self.backend
            {
                let (remove_ids, additions) = clause_delta(clauses, ids, &candidate.clauses);
                match with_route_environment(&route_after, || {
                    classifier.apply_change(&remove_ids, additions)
                })? {
                    Ok(change) => {
                        let classification = map_incremental_result(&candidate, classifier.result());
                        *clauses = candidate.clauses.clone();
                        *ids = classifier.clause_ids();
                        self.revision += 1;
                        self.route = route_after.clone();
                        self.frontend = candidate;
                        self.classification = classification;
                        return Ok(receipt_from_change(
                            self.revision,
                            route_before,
                            route_after,
                            change,
                        ));
                    }
                    Err(_) => {
                        // The retained adapter declined.  Exact classification
                        // below is the transactional fallback; no partial state
                        // from a failed IncrementalClassifier operation commits.
                    }
                }
            }

            if let Ok(classifier) = with_route_environment(&route_after, || {
                IncrementalClassifier::new(candidate.clauses.clone())
            })? {
                let classification = map_incremental_result(&candidate, classifier.result());
                let ids = classifier.clause_ids();
                let added = candidate.clauses.len();
                self.revision += 1;
                self.route = route_after.clone();
                self.frontend = candidate;
                self.classification = classification;
                self.backend = SourceBackend::Incremental {
                    clauses: self.frontend.clauses.clone(),
                    classifier,
                    ids,
                };
                return Ok(SourceIncrementalReceipt {
                    revision: self.revision,
                    route_migrated: route_before != route_after,
                    route_before,
                    route_after,
                    strategy: ChangeStrategy::ExactRebuild,
                    reused_fixpoint: false,
                    reused_subsumptions: 0,
                    reused_edges: 0,
                    added_normalized_clauses: added,
                    removed_normalized_clauses: 0,
                    meaningful_incremental_update: false,
                });
            }
        }

        let classification = classify_source_exact(source)?;
        let removed = self.frontend.clauses.len();
        let added = candidate.clauses.len();
        self.revision += 1;
        self.route = route_after.clone();
        self.frontend = candidate;
        self.classification = classification;
        self.backend = SourceBackend::ExactBatch;
        Ok(SourceIncrementalReceipt {
            revision: self.revision,
            route_migrated: route_before != route_after,
            route_before,
            route_after,
            strategy: ChangeStrategy::ExactRebuild,
            reused_fixpoint: false,
            reused_subsumptions: 0,
            reused_edges: 0,
            added_normalized_clauses: added,
            removed_normalized_clauses: removed,
            meaningful_incremental_update: false,
        })
    }

    pub fn classification(&self) -> &Classification {
        &self.classification
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn route(&self) -> &str {
        &self.route
    }

    pub fn retained_backend(&self) -> bool {
        matches!(self.backend, SourceBackend::Incremental { .. })
    }
}

fn receipt_from_change(
    revision: u64,
    route_before: String,
    route_after: String,
    change: IncrementalChange,
) -> SourceIncrementalReceipt {
    let meaningful = matches!(
        change.strategy,
        ChangeStrategy::ElDelta | ChangeStrategy::CbDelta | ChangeStrategy::HtDelta
    );
    SourceIncrementalReceipt {
        revision,
        route_migrated: route_before != route_after,
        route_before,
        route_after,
        strategy: change.strategy,
        reused_fixpoint: change.reused_fixpoint,
        reused_subsumptions: change.reused_subsumptions,
        reused_edges: change.reused_edges,
        added_normalized_clauses: change.added_clauses,
        removed_normalized_clauses: change.removed_clauses,
        meaningful_incremental_update: meaningful,
    }
}

/// The lower-level retained state is complete only for routes whose semantics
/// are entirely represented by the normalized clauses.  Typed HT adapters will
/// relax these exclusions one route at a time while preserving this gate.
fn clause_state_is_complete(frontend: &FrontendResult) -> bool {
    let route = frontend.route.as_str();
    let clause_route = route == "elc"
        || route == "elc_cert"
        || route == "certified_el_production"
        || route == "production_all"
        || route == "production_all8"
        || route == "production_all1"
        || route.starts_with("cb_")
        || route == "seq_on"
        || route == "seq_off";
    clause_route
        && frontend.cardinalities.is_empty()
        && frontend.rules.is_empty()
        && frontend.nominal_abox.is_empty()
        && frontend.profile.source.abox_axioms == 0
}

fn normalize_automatic(source: &str) -> Result<FrontendResult, String> {
    let _guard = crate::routing::EnvironmentGuard::capture();
    std::env::set_var("KM_ROUTE", "auto");
    crate::frontend::ofn_to_clauses(source).map_err(|error| error.0)
}

fn classify_source_exact(source: &str) -> Result<Classification, String> {
    let path = crate::orchestrate::tmpfile::TempPath::new(".ofn");
    std::fs::write(path.path(), source).map_err(|error| error.to_string())?;
    let _guard = crate::routing::EnvironmentGuard::capture();
    std::env::set_var("KM_ROUTE", "auto");
    let cfg = Config::from_env();
    crate::orchestrate::classify(&cfg, path.path()).map_err(|error| error.to_string())
}

fn with_route_environment<T>(
    route: &str,
    operation: impl FnOnce() -> T,
) -> Result<T, String> {
    let _guard = crate::routing::EnvironmentGuard::capture();
    let route = route
        .parse::<crate::routing::Route>()
        .map_err(|error| format!("invalid selected incremental route {route:?}: {error}"))?;
    route.apply_environment();
    Ok(operation())
}

fn clause_delta(
    old: &[JClause],
    ids: &[ClauseId],
    new: &[JClause],
) -> (Vec<ClauseId>, Vec<JClause>) {
    debug_assert_eq!(old.len(), ids.len());
    // Match duplicate occurrences by their stable old order. A linear scan for
    // every candidate clause made a no-op transaction quadratic on large OWL
    // sources, which defeats an incremental API before saturation begins.
    let mut available: HashMap<&JClause, VecDeque<usize>> = HashMap::new();
    for (index, clause) in old.iter().enumerate() {
        available.entry(clause).or_default().push_back(index);
    }
    let mut used = vec![false; old.len()];
    let mut additions = Vec::new();
    for clause in new {
        if let Some(index) = available.get_mut(clause).and_then(VecDeque::pop_front) {
            used[index] = true;
        } else {
            additions.push(clause.clone());
        }
    }
    let removals = ids
        .iter()
        .enumerate()
        .filter_map(|(index, id)| (!used[index]).then_some(*id))
        .collect();
    (removals, additions)
}

fn map_incremental_result(
    frontend: &FrontendResult,
    result: crate::incremental::IncrementalResult,
) -> Classification {
    let named: BTreeSet<&str> = frontend.named.iter().map(String::as_str).collect();
    let asserted: BTreeSet<&str> = frontend.asserted_classes.iter().map(String::as_str).collect();
    let is_internal = |name: &str| {
        !named.contains(name)
            && (name.starts_with("Q_")
                || name.starts_with("__")
                || name.starts_with("aux_")
                || name.starts_with("def_")
                || (name.contains(':') && !is_bottom(name)))
    };
    let mapped = |name: &str| {
        frontend
            .iri_map
            .get(name)
            .map_or_else(|| name.to_string(), Clone::clone)
    };
    let mut subsumptions = BTreeSet::new();
    let mut unsatisfiable = BTreeSet::new();
    let mut asserted_unsat = false;
    for (subject, supers) in result.subsumptions {
        if is_internal(&subject) {
            continue;
        }
        for superclass in supers {
            if is_bottom(&superclass) {
                unsatisfiable.insert(mapped(&subject));
                asserted_unsat |= asserted.contains(subject.as_str());
            } else if !is_internal(&superclass) && subject != superclass {
                subsumptions.insert([mapped(&subject), mapped(&superclass)]);
            }
        }
    }
    Classification {
        consistent: !result.inconsistent && !asserted_unsat,
        subsumptions: if asserted_unsat {
            Vec::new()
        } else {
            subsumptions.into_iter().collect()
        },
        unsatisfiable: if asserted_unsat {
            Vec::new()
        } else {
            unsatisfiable.into_iter().collect()
        },
        dropped: result.dropped,
    }
}

fn is_bottom(name: &str) -> bool {
    name == "owl:Nothing"
        || name == "http://www.w3.org/2002/07/owl#Nothing"
        || name == "\u{22a5}"
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum SourceCommand {
    Init { functional_syntax: String },
    Replace { functional_syntax: String },
    Classify,
    Stats,
}

pub fn run_jsonl_session<R: BufRead, W: Write>(reader: R, mut writer: W) -> std::io::Result<()> {
    let mut session: Option<SourceIncrementalClassifier> = None;
    for line in reader.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let response = match serde_json::from_str::<SourceCommand>(&line) {
            Ok(SourceCommand::Init { functional_syntax }) => {
                match SourceIncrementalClassifier::new(&functional_syntax) {
                    Ok(classifier) => {
                        let response = session_response("init", &classifier, None);
                        session = Some(classifier);
                        response
                    }
                    Err(error) => error_response("init", error),
                }
            }
            Ok(SourceCommand::Replace { functional_syntax }) => match session.as_mut() {
                Some(classifier) => match classifier.replace_source(&functional_syntax) {
                    Ok(receipt) => session_response("replace", classifier, Some(receipt)),
                    Err(error) => error_response("replace", error),
                },
                None => error_response("replace", "session is not initialised"),
            },
            Ok(SourceCommand::Classify) => match session.as_ref() {
                Some(classifier) => session_response("classify", classifier, None),
                None => error_response("classify", "session is not initialised"),
            },
            Ok(SourceCommand::Stats) => match session.as_ref() {
                Some(classifier) => json!({
                    "status": "ok",
                    "op": "stats",
                    "revision": classifier.revision(),
                    "route": classifier.route(),
                    "retained_backend": classifier.retained_backend(),
                }),
                None => error_response("stats", "session is not initialised"),
            },
            Err(error) => error_response("parse", error.to_string()),
        };
        serde_json::to_writer(&mut writer, &response)
            .map_err(|error| std::io::Error::new(std::io::ErrorKind::InvalidData, error))?;
        writer.write_all(b"\n")?;
        writer.flush()?;
    }
    Ok(())
}

fn session_response(
    op: &str,
    classifier: &SourceIncrementalClassifier,
    receipt: Option<SourceIncrementalReceipt>,
) -> Value {
    json!({
        "status": "ok",
        "op": op,
        "revision": classifier.revision(),
        "route": classifier.route(),
        "retained_backend": classifier.retained_backend(),
        "receipt": receipt,
        "result": classifier.classification(),
    })
}

fn error_response(op: &str, error: impl Into<String>) -> Value {
    json!({"status": "error", "op": op, "error": error.into()})
}

#[cfg(test)]
mod tests {
    use super::{clause_delta, run_jsonl_session, SourceIncrementalClassifier};
    use crate::incremental::ChangeStrategy;
    use crate::json_io::{JAtom, JClause, JTerm};

    fn fact(name: &str) -> JClause {
        JClause {
            body: Vec::new(),
            head: vec![JAtom::Concept {
                concept: name.to_string(),
                term: JTerm::Var { name: "x".into() },
            }],
        }
    }

    #[test]
    fn multiset_delta_preserves_duplicate_clause_identity() {
        let a = fact("A");
        let b = fact("B");
        let (removed, added) = clause_delta(
            &[a.clone(), a.clone(), b.clone()],
            &[7, 8, 9],
            &[a, b.clone(), b],
        );
        assert_eq!(removed, vec![8]);
        assert_eq!(added.len(), 1);
    }

    #[test]
    fn complete_source_el_addition_reuses_the_fixpoint() {
        let before = r#"Ontology(
 Declaration(Class(<http://example.org/A>))
 Declaration(Class(<http://example.org/B>))
 SubClassOf(<http://example.org/A> <http://example.org/B>)
)"#;
        let after = r#"Ontology(
 Declaration(Class(<http://example.org/A>))
 Declaration(Class(<http://example.org/B>))
 Declaration(Class(<http://example.org/C>))
 SubClassOf(<http://example.org/A> <http://example.org/B>)
 SubClassOf(<http://example.org/B> <http://example.org/C>)
)"#;
        let mut session = SourceIncrementalClassifier::new(before).unwrap();
        assert!(session.retained_backend());
        let receipt = session.replace_source(after).unwrap();
        assert_eq!(receipt.strategy, ChangeStrategy::ElDelta);
        assert!(receipt.meaningful_incremental_update);
        assert!(session.classification().subsumptions.iter().any(|pair| {
            pair == &["http://example.org/A".to_string(), "http://example.org/C".to_string()]
        }));
    }

    #[test]
    fn jsonl_session_publishes_a_transaction_receipt() {
        let before = "Prefix(:=<http://example.org/>)\nOntology(\nSubClassOf(:A :B)\n)";
        let after = "Prefix(:=<http://example.org/>)\nOntology(\nSubClassOf(:A :B)\nSubClassOf(:B :C)\n)";
        let commands = format!(
            "{}\n{}\n",
            serde_json::json!({"op": "init", "functional_syntax": before}),
            serde_json::json!({"op": "replace", "functional_syntax": after}),
        );
        let mut output = Vec::new();
        run_jsonl_session(std::io::Cursor::new(commands), &mut output).unwrap();
        let responses: Vec<serde_json::Value> = String::from_utf8(output)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        assert_eq!(responses.len(), 2);
        assert_eq!(responses[1]["status"], "ok");
        assert_eq!(responses[1]["receipt"]["revision"], 1);
        assert_eq!(
            responses[1]["receipt"]["meaningful_incremental_update"],
            true
        );
    }

    #[test]
    fn typed_abox_state_never_enters_the_clause_only_adapter() {
        let source = r#"Ontology(
 Declaration(Class(<http://example.org/A>))
 Declaration(NamedIndividual(<http://example.org/i>))
 ClassAssertion(<http://example.org/A> <http://example.org/i>)
)"#;
        let frontend = super::normalize_automatic(source).unwrap();
        assert!(frontend.profile.source.abox_axioms > 0);
        assert!(!super::clause_state_is_complete(&frontend));
    }

    #[test]
    fn automatic_production_portfolio_reuses_its_complete_cb_state() {
        let before = r#"Ontology(
 SubClassOf(<http://example.org/A>
   ObjectUnionOf(<http://example.org/B> <http://example.org/C>))
 SubClassOf(<http://example.org/B> <http://example.org/D>)
 SubClassOf(<http://example.org/C> <http://example.org/D>)
)"#;
        let after = r#"Ontology(
 SubClassOf(<http://example.org/A>
   ObjectUnionOf(<http://example.org/B> <http://example.org/C>))
 SubClassOf(<http://example.org/B> <http://example.org/D>)
 SubClassOf(<http://example.org/C> <http://example.org/D>)
 SubClassOf(<http://example.org/B> <http://example.org/E>)
 SubClassOf(<http://example.org/C> <http://example.org/E>)
)"#;
        let mut session = SourceIncrementalClassifier::new(before).unwrap();
        assert_eq!(session.route(), "production_all");
        assert!(session.retained_backend());
        let receipt = session.replace_source(after).unwrap();
        assert_eq!(receipt.strategy, ChangeStrategy::CbDelta);
        assert!(receipt.meaningful_incremental_update);
        assert!(session.classification().subsumptions.iter().any(|pair| {
            pair == &["http://example.org/A".to_string(), "http://example.org/E".to_string()]
        }));
    }
}
