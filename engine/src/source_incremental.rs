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
use crate::incremental_ht::{HtChangeKind, IncrementalHtClassifier};
use crate::incremental_positive_abox::IncrementalPositiveAboxClassifier;
use crate::incremental_rules::IncrementalRulesClassifier;
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
    pub added_rules: usize,
    pub removed_rules: usize,
    /// `false` identifies an honest batch safety fallback, never hidden reuse.
    pub meaningful_incremental_update: bool,
}

enum SourceBackend {
    Incremental {
        classifier: IncrementalClassifier,
        clauses: Vec<JClause>,
        ids: Vec<ClauseId>,
    },
    PositiveAbox(IncrementalPositiveAboxClassifier),
    TypedHt {
        classifier: IncrementalHtClassifier,
        clauses: Vec<JClause>,
    },
    Rules(IncrementalRulesClassifier),
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
        if route == "elc" && !frontend.abox_inconsistent {
            if let Some((classifier, result, consistent)) =
                IncrementalPositiveAboxClassifier::new(&frontend)
            {
                let mut classification = map_el_result(&frontend, result);
                classification.consistent = consistent;
                return Ok(Self {
                    revision: 0,
                    route,
                    frontend,
                    classification,
                    backend: SourceBackend::PositiveAbox(classifier),
                });
            }
        }
        if let Some(input) = with_route_environment(&route, || {
            crate::orchestrate::race::prepare_incremental_ht(&frontend)
        })? {
            if let Ok(classifier) = IncrementalHtClassifier::new_typed(&frontend.clauses, input) {
                let classification = map_incremental_result(&frontend, classifier.result());
                return Ok(Self {
                    revision: 0,
                    route,
                    frontend,
                    classification,
                    backend: SourceBackend::TypedHt {
                        classifier,
                        clauses: Vec::new(),
                    },
                }
                .with_live_clauses());
            }
        }
        let classification = classify_source_exact(source)?;
        let backend = if route == "ht_rules" {
            SourceBackend::Rules(IncrementalRulesClassifier::new(
                &frontend,
                classification.clone(),
            ))
        } else {
            SourceBackend::ExactBatch
        };
        Ok(Self {
            revision: 0,
            route,
            frontend,
            classification,
            backend,
        })
    }

    fn with_live_clauses(mut self) -> Self {
        if let SourceBackend::Incremental { clauses, .. } = &mut self.backend {
            *clauses = self.frontend.clauses.clone();
        }
        if let SourceBackend::TypedHt { clauses, .. } = &mut self.backend {
            *clauses = self.frontend.clauses.clone();
        }
        self
    }

    /// Atomically replace the complete flattened source ontology.
    pub fn replace_source(&mut self, source: &str) -> Result<SourceIncrementalReceipt, String> {
        let candidate = normalize_automatic(source)?;
        let route_before = self.route.clone();
        let route_after = candidate.route.clone();

        if let SourceBackend::PositiveAbox(classifier) = &mut self.backend {
            if let Some(update) = classifier.update(&candidate)? {
                let (removed, added) =
                    clause_change_counts(&self.frontend.clauses, &candidate.clauses);
                let (removed_rules, added_rules) =
                    sequence_change_counts(&self.frontend.rules, &candidate.rules);
                let meaningful = update.stats.reused_fixpoint;
                let mut classification = map_el_result(&candidate, update.result);
                classification.consistent = update.consistent;
                self.revision += 1;
                self.route = route_after.clone();
                self.frontend = candidate;
                self.classification = classification;
                return Ok(SourceIncrementalReceipt {
                    revision: self.revision,
                    route_migrated: route_before != route_after,
                    route_before,
                    route_after,
                    strategy: if meaningful {
                        ChangeStrategy::ElDelta
                    } else {
                        ChangeStrategy::ExactRebuild
                    },
                    reused_fixpoint: update.stats.reused_fixpoint,
                    reused_subsumptions: update.stats.reused_subsumptions,
                    reused_edges: update.stats.reused_edges,
                    added_normalized_clauses: added,
                    removed_normalized_clauses: removed,
                    added_rules,
                    removed_rules,
                    meaningful_incremental_update: meaningful,
                });
            }
        }

        let typed_ht_input = with_route_environment(&route_after, || {
            crate::orchestrate::race::prepare_incremental_ht(&candidate)
        })?;
        if let (
            SourceBackend::TypedHt {
                classifier,
                clauses,
            },
            Some(input),
        ) = (&self.backend, typed_ht_input)
        {
            let old_ids: Vec<ClauseId> = (0..clauses.len() as ClauseId).collect();
            let (removed_ids, additions) = clause_delta(clauses, &old_ids, &candidate.clauses);
            let removed_clauses: Vec<JClause> = removed_ids
                .iter()
                .filter_map(|id| clauses.get(*id as usize).cloned())
                .collect();
            let mut changed = removed_clauses;
            changed.extend(additions.iter().cloned());
            let kind = match (removed_ids.is_empty(), additions.is_empty()) {
                (true, false) => HtChangeKind::Addition,
                (false, true) => HtChangeKind::Removal,
                _ => HtChangeKind::Replacement,
            };
            if let Ok((next, stats)) =
                classifier.updated_typed(&candidate.clauses, &changed, kind, input)
            {
                let classification = map_incremental_result(&candidate, next.result());
                self.revision += 1;
                self.route = route_after.clone();
                self.frontend = candidate;
                self.classification = classification;
                self.backend = SourceBackend::TypedHt {
                    classifier: next,
                    clauses: self.frontend.clauses.clone(),
                };
                let meaningful = stats.reused_probes > 0 || stats.resumed_models > 0;
                return Ok(SourceIncrementalReceipt {
                    revision: self.revision,
                    route_migrated: route_before != route_after,
                    route_before,
                    route_after,
                    strategy: if meaningful {
                        ChangeStrategy::HtDelta
                    } else {
                        ChangeStrategy::ExactRebuild
                    },
                    reused_fixpoint: meaningful,
                    reused_subsumptions: stats.reused_subsumptions,
                    reused_edges: stats.reused_edges,
                    added_normalized_clauses: additions.len(),
                    removed_normalized_clauses: removed_ids.len(),
                    added_rules: 0,
                    removed_rules: 0,
                    meaningful_incremental_update: meaningful,
                });
            }
        }

        if let SourceBackend::Rules(classifier) = &self.backend {
            if let Some(update) = classifier.updated(&candidate)? {
                let (removed, added) =
                    clause_change_counts(&self.frontend.clauses, &candidate.clauses);
                let (removed_rules, added_rules) =
                    sequence_change_counts(&self.frontend.rules, &candidate.rules);
                let reused_subsumptions = update.reused_subsumptions;
                let reused_fixpoint = update.probe_reused;
                let retained_taxonomy = update.retained_taxonomy;
                let classification = update.classification;
                self.revision += 1;
                self.route = route_after.clone();
                self.frontend = candidate;
                self.classification = classification.clone();
                self.backend = SourceBackend::Rules(IncrementalRulesClassifier::with_taxonomy(
                    &self.frontend,
                    classification,
                    retained_taxonomy,
                ));
                return Ok(SourceIncrementalReceipt {
                    revision: self.revision,
                    route_migrated: route_before != route_after,
                    route_before,
                    route_after,
                    strategy: ChangeStrategy::HtDelta,
                    reused_fixpoint,
                    reused_subsumptions,
                    reused_edges: 0,
                    added_normalized_clauses: added,
                    removed_normalized_clauses: removed,
                    added_rules,
                    removed_rules,
                    meaningful_incremental_update: true,
                });
            }
        }

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
                        let classification =
                            map_incremental_result(&candidate, classifier.result());
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
                let (removed, added) =
                    clause_change_counts(&self.frontend.clauses, &candidate.clauses);
                let (removed_rules, added_rules) =
                    sequence_change_counts(&self.frontend.rules, &candidate.rules);
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
                    removed_normalized_clauses: removed,
                    added_rules,
                    removed_rules,
                    meaningful_incremental_update: false,
                });
            }
        }

        if let Some(input) = with_route_environment(&route_after, || {
            crate::orchestrate::race::prepare_incremental_ht(&candidate)
        })? {
            if let Ok(classifier) = IncrementalHtClassifier::new_typed(&candidate.clauses, input) {
                let classification = map_incremental_result(&candidate, classifier.result());
                let (removed, added) =
                    clause_change_counts(&self.frontend.clauses, &candidate.clauses);
                let (removed_rules, added_rules) =
                    sequence_change_counts(&self.frontend.rules, &candidate.rules);
                self.revision += 1;
                self.route = route_after.clone();
                self.frontend = candidate;
                self.classification = classification;
                self.backend = SourceBackend::TypedHt {
                    classifier,
                    clauses: self.frontend.clauses.clone(),
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
                    removed_normalized_clauses: removed,
                    added_rules,
                    removed_rules,
                    meaningful_incremental_update: false,
                });
            }
        }

        let classification = classify_source_exact(source)?;
        let removed = self.frontend.clauses.len();
        let added = candidate.clauses.len();
        let removed_rules = self.frontend.rules.len();
        let added_rules = candidate.rules.len();
        self.revision += 1;
        self.route = route_after.clone();
        self.frontend = candidate;
        self.classification = classification;
        self.backend = if route_after == "elc" && !self.frontend.abox_inconsistent {
            IncrementalPositiveAboxClassifier::new(&self.frontend)
                .map(|(classifier, _, _)| SourceBackend::PositiveAbox(classifier))
                .unwrap_or(SourceBackend::ExactBatch)
        } else if route_after == "ht_rules" {
            SourceBackend::Rules(IncrementalRulesClassifier::new(
                &self.frontend,
                self.classification.clone(),
            ))
        } else {
            SourceBackend::ExactBatch
        };
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
            added_rules,
            removed_rules,
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
        matches!(
            self.backend,
            SourceBackend::Incremental { .. }
                | SourceBackend::PositiveAbox(_)
                | SourceBackend::TypedHt { .. }
                | SourceBackend::Rules(_)
        )
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
        added_rules: 0,
        removed_rules: 0,
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
        && frontend.rbox.is_empty()
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

fn with_route_environment<T>(route: &str, operation: impl FnOnce() -> T) -> Result<T, String> {
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

fn clause_change_counts(old: &[JClause], new: &[JClause]) -> (usize, usize) {
    let ids: Vec<ClauseId> = (0..old.len() as ClauseId).collect();
    let (removed, added) = clause_delta(old, &ids, new);
    (removed.len(), added.len())
}

fn sequence_change_counts<T: PartialEq>(old: &[T], new: &[T]) -> (usize, usize) {
    let mut used = vec![false; old.len()];
    let mut additions = 0;
    for candidate in new {
        if let Some(index) = old
            .iter()
            .enumerate()
            .find_map(|(index, item)| (!used[index] && item == candidate).then_some(index))
        {
            used[index] = true;
        } else {
            additions += 1;
        }
    }
    (used.iter().filter(|used| !**used).count(), additions)
}

fn map_incremental_result(
    frontend: &FrontendResult,
    result: crate::incremental::IncrementalResult,
) -> Classification {
    let named: BTreeSet<&str> = frontend.named.iter().map(String::as_str).collect();
    let asserted: BTreeSet<&str> = frontend
        .asserted_classes
        .iter()
        .map(String::as_str)
        .collect();
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

fn map_el_result(frontend: &FrontendResult, result: crate::elcomplete::ElResult) -> Classification {
    map_incremental_result(
        frontend,
        crate::incremental::IncrementalResult::from_el(result),
    )
}

fn is_bottom(name: &str) -> bool {
    name == "owl:Nothing" || name == "http://www.w3.org/2002/07/owl#Nothing" || name == "\u{22a5}"
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

    static ENV_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

    fn lock_environment() -> std::sync::MutexGuard<'static, ()> {
        ENV_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

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
        let _environment = lock_environment();
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
            pair == &[
                "http://example.org/A".to_string(),
                "http://example.org/C".to_string(),
            ]
        }));
    }

    #[test]
    fn complete_source_el_removal_retains_an_independent_component() {
        let _environment = lock_environment();
        let before = r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(Class(:X)) Declaration(Class(:Y))
 SubClassOf(:A :B) SubClassOf(:B :C) SubClassOf(:X :Y)
)"#;
        let after = r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))
 Declaration(Class(:X)) Declaration(Class(:Y))
 SubClassOf(:A :B) SubClassOf(:X :Y)
)"#;
        let mut session = SourceIncrementalClassifier::new(before).unwrap();
        let receipt = session.replace_source(after).unwrap();
        assert_eq!(receipt.strategy, ChangeStrategy::ElDelta);
        assert!(receipt.meaningful_incremental_update);
        assert!(receipt.reused_subsumptions > 0);
        assert!(!session.classification().subsumptions.iter().any(|pair| {
            pair == &[
                "http://example.org/A".to_string(),
                "http://example.org/C".to_string(),
            ]
        }));
        assert!(session.classification().subsumptions.iter().any(|pair| {
            (pair[0] == "http://example.org/X" || pair[0] == ":X")
                && (pair[1] == "http://example.org/Y" || pair[1] == ":Y")
        }));
    }

    #[test]
    fn jsonl_session_publishes_a_transaction_receipt() {
        let _environment = lock_environment();
        let before = "Prefix(:=<http://example.org/>)\nOntology(\nSubClassOf(:A :B)\n)";
        let after =
            "Prefix(:=<http://example.org/>)\nOntology(\nSubClassOf(:A :B)\nSubClassOf(:B :C)\n)";
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
        let _environment = lock_environment();
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
    fn positive_el_abox_updates_reuse_typed_completion_state() {
        let _environment = lock_environment();
        let terminology = (0..1_000)
            .map(|index| {
                format!("SubClassOf(<Seed{index}> ObjectSomeValuesFrom(<r> <Leaf{index}>))")
            })
            .collect::<Vec<_>>()
            .join("\n");
        let consistent = format!(
            r#"Ontology(
 Declaration(Class(<A>)) Declaration(Class(<B>)) Declaration(Class(<C>))
 Declaration(Class(<X>)) Declaration(Class(<Y>))
 Declaration(NamedIndividual(<a>))
 SubClassOf(<A> <B>) DisjointClasses(<B> <C>) SubClassOf(<X> <Y>)
 {terminology}
 ClassAssertion(<A> <a>)
)"#
        );
        let inconsistent = format!(
            r#"Ontology(
 Declaration(Class(<A>)) Declaration(Class(<B>)) Declaration(Class(<C>))
 Declaration(Class(<X>)) Declaration(Class(<Y>))
 Declaration(NamedIndividual(<a>))
 SubClassOf(<A> <B>) DisjointClasses(<B> <C>) SubClassOf(<X> <Y>)
 {terminology}
 ClassAssertion(<A> <a>) ClassAssertion(<C> <a>)
)"#
        );
        let mut session = SourceIncrementalClassifier::new(&consistent).unwrap();
        assert_eq!(session.route(), "elc");
        assert!(session.retained_backend());
        assert!(session.classification().consistent);
        let initial = session.classification().clone();

        let addition = session.replace_source(&inconsistent).unwrap();
        assert_eq!(addition.strategy, ChangeStrategy::ElDelta);
        assert!(addition.meaningful_incremental_update);
        assert!(!session.classification().consistent);

        let removal = session.replace_source(&consistent).unwrap();
        assert_eq!(removal.strategy, ChangeStrategy::ElDelta);
        assert!(removal.meaningful_incremental_update);
        assert_eq!(session.classification(), &initial);
    }

    #[test]
    fn automatic_production_portfolio_reuses_its_complete_cb_state() {
        let _environment = lock_environment();
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
            pair == &[
                "http://example.org/A".to_string(),
                "http://example.org/E".to_string(),
            ]
        }));
    }

    #[test]
    fn typed_ht_source_preparation_reuses_unaffected_probes() {
        let _environment = lock_environment();
        let before = r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:D))
 Declaration(Class(:E)) Declaration(Class(:F)) Declaration(ObjectProperty(:r))
 TransitiveObjectProperty(:r)
 SubClassOf(:A ObjectAllValuesFrom(:r :B))
 SubClassOf(:D :E)
)"#;
        let after = r#"Prefix(:=<http://example.org/>)
Ontology(
 Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:D))
 Declaration(Class(:E)) Declaration(Class(:F)) Declaration(ObjectProperty(:r))
 TransitiveObjectProperty(:r)
 SubClassOf(:A ObjectAllValuesFrom(:r :B))
 SubClassOf(:D :E)
 SubClassOf(:E :F)
)"#;
        let _guard = crate::routing::EnvironmentGuard::capture();
        crate::routing::Route::HtGeneral.apply_environment();
        let old = crate::frontend::ofn_to_clauses(before).unwrap();
        let new = crate::frontend::ofn_to_clauses(after).unwrap();
        let old_input = crate::orchestrate::race::prepare_incremental_ht(&old).unwrap();
        let new_input = crate::orchestrate::race::prepare_incremental_ht(&new).unwrap();
        let classifier =
            crate::incremental_ht::IncrementalHtClassifier::new_typed(&old.clauses, old_input)
                .unwrap();
        let old_ids: Vec<crate::incremental::ClauseId> =
            (0..old.clauses.len() as crate::incremental::ClauseId).collect();
        let (_, additions) = clause_delta(&old.clauses, &old_ids, &new.clauses);
        let (_, stats) = classifier
            .updated_typed(
                &new.clauses,
                &additions,
                crate::incremental_ht::HtChangeKind::Addition,
                new_input,
            )
            .unwrap();
        assert!(stats.reused_probes > 0 || stats.resumed_models > 0);
    }
}
