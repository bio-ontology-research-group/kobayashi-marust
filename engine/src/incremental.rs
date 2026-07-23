//! Stateful incremental reasoning over KM's exact EL++ and CB fragments.
//!
//! [`IncrementalClassifier`] is the public all-fragment API. It keeps the
//! existing addition-only EL++ delta implementation when the complete snapshot
//! remains in EL++. For the general consequence-based fragment, ordering-stable
//! monotone additions fork and resume the completed context graph, replaying
//! retained premises against the new ontology indexes. Removals always rebuild
//! because the CB and EL stores do not yet retain dependency sets that could
//! invalidate every consequence of a deleted clause. Insertions that change a
//! retained ordering/nominal invariant also rebuild explicitly. No operation
//! exposes a stale or partial classification.
//!
//! [`run_jsonl_session`] supplies the `km incremental` transport. It consumes
//! the same normalised [`JClause`] values as `km elc` and `km engine`. Every
//! accepted clause receives a stable, non-reused session id for later removal.

use std::collections::{BTreeMap, BTreeSet};
use std::io::{BufRead, Write};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

use crate::json_io::{JAtom, JClause};
use crate::reasoner::{Reasoner, RetainedCbBoundary, RetainedCbReasoner};

pub use crate::elcomplete::{IncrementalElClassifier, IncrementalError, IncrementalUpdate};

/// Stable identifier for one clause in an incremental session.
pub type ClauseId = u64;

/// Exact engine currently serving the snapshot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum IncrementalBackend {
    El,
    Cb,
}

/// How an accepted change produced its new fixpoint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ChangeStrategy {
    NoOp,
    ElDelta,
    CbDelta,
    ExactRebuild,
}

/// Complete classification returned by the incremental API.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct IncrementalResult {
    pub subsumptions: BTreeMap<String, Vec<String>>,
    pub inconsistent: bool,
    /// Always zero for an accepted session. A fresh CB build with dropped
    /// clauses is rejected instead of publishing an incomplete answer.
    pub dropped: usize,
    /// Reserved for parity with the ELC worker response. The general API only
    /// accepts exact snapshots, so this is always empty.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub unresolved: Vec<String>,
}

impl IncrementalResult {
    fn from_el(result: crate::elcomplete::ElResult) -> Self {
        IncrementalResult {
            subsumptions: result.subsumptions,
            inconsistent: result.inconsistent,
            dropped: 0,
            unresolved: result.unresolved,
        }
    }

    fn pair_count(&self) -> usize {
        self.subsumptions.values().map(Vec::len).sum()
    }
}

/// Receipt for one atomic addition or removal transaction.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub struct IncrementalChange {
    pub revision: u64,
    pub added_clauses: usize,
    pub removed_clauses: usize,
    pub total_clauses: usize,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub added_clause_ids: Vec<ClauseId>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub removed_clause_ids: Vec<ClauseId>,
    pub backend_before: IncrementalBackend,
    pub backend_after: IncrementalBackend,
    pub strategy: ChangeStrategy,
    pub reused_fixpoint: bool,
    pub reused_subsumptions: usize,
    /// Retained completion-role edges for EL, or retained context successor
    /// edges for CB.
    pub reused_edges: usize,
    /// Facts added beyond a retained EL state, or the complete fresh answer
    /// size when `strategy == exact_rebuild`.
    pub new_subsumptions: usize,
    /// New completion-role edges for EL, or new context successor edges for CB.
    pub new_edges: usize,
}

/// Error that leaves the preceding session revision unchanged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum IncrementalReasoningError {
    /// The CB parser dropped clauses outside its supported normal form. The
    /// sound but incomplete residue is never exposed by this API.
    UnsupportedClauses {
        dropped: usize,
    },
    /// A resource backstop stopped CB saturation before its fixpoint.
    IncompleteFixpoint,
    UnknownClauseIds {
        ids: Vec<ClauseId>,
    },
    DuplicateClauseIds {
        ids: Vec<ClauseId>,
    },
    ClauseIdExhausted,
}

impl std::fmt::Display for IncrementalReasoningError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IncrementalReasoningError::UnsupportedClauses { dropped } => write!(
                f,
                "incremental CB mode rejected {dropped} unsupported clause(s)"
            ),
            IncrementalReasoningError::IncompleteFixpoint => write!(
                f,
                "incremental CB mode reached a resource backstop before fixpoint"
            ),
            IncrementalReasoningError::UnknownClauseIds { ids } => {
                write!(f, "unknown clause id(s): {ids:?}")
            }
            IncrementalReasoningError::DuplicateClauseIds { ids } => {
                write!(f, "duplicate clause id(s): {ids:?}")
            }
            IncrementalReasoningError::ClauseIdExhausted => {
                write!(f, "incremental clause id space exhausted")
            }
        }
    }
}

impl std::error::Error for IncrementalReasoningError {}

struct StoredClause {
    id: ClauseId,
    clause: JClause,
}

enum CbBackendState {
    Retained {
        reasoner: RetainedCbReasoner,
        result: IncrementalResult,
    },
    Snapshot(IncrementalResult),
}

impl CbBackendState {
    fn result(&self) -> IncrementalResult {
        match self {
            CbBackendState::Retained { result, .. } => result.clone(),
            CbBackendState::Snapshot(result) => result.clone(),
        }
    }

    fn result_ref(&self) -> &IncrementalResult {
        match self {
            CbBackendState::Retained { result, .. } | CbBackendState::Snapshot(result) => result,
        }
    }

    fn add_retained(
        &mut self,
        additions: &[JClause],
    ) -> Option<Result<crate::engine::RetainedInsertStats, RetainedCbBoundary>> {
        match self {
            CbBackendState::Retained { reasoner, result } => {
                let update = reasoner.add_clauses(additions);
                if update.is_ok() {
                    *result = result_from_retained_cb(reasoner);
                }
                Some(update)
            }
            CbBackendState::Snapshot(_) => None,
        }
    }
}

enum BackendState {
    El(IncrementalElClassifier),
    Cb(CbBackendState),
}

impl BackendState {
    fn kind(&self) -> IncrementalBackend {
        match self {
            BackendState::El(_) => IncrementalBackend::El,
            BackendState::Cb(_) => IncrementalBackend::Cb,
        }
    }

    fn result(&self) -> IncrementalResult {
        match self {
            BackendState::El(classifier) => IncrementalResult::from_el(classifier.result()),
            BackendState::Cb(state) => state.result(),
        }
    }

    fn pair_count(&self) -> usize {
        match self {
            BackendState::El(classifier) => {
                IncrementalResult::from_el(classifier.result()).pair_count()
            }
            BackendState::Cb(state) => state.result_ref().pair_count(),
        }
    }

    fn inconsistent(&self) -> bool {
        match self {
            BackendState::El(classifier) => classifier.is_inconsistent(),
            BackendState::Cb(state) => state.result_ref().inconsistent,
        }
    }
}

/// Exact incremental classifier for every normalised clause set accepted by
/// KM's EL++ or consequence-based worker.
///
/// Pure-EL additions reuse the existing completion state. Ordering-stable CB
/// additions fork and resume the existing context graph. An EL-to-CB
/// transition, every removal, and CB insertions outside the retained-state
/// proof boundary construct a fresh candidate reasoner. Every path commits only
/// after a complete fixpoint is available, and its strategy is visible in
/// [`IncrementalChange::strategy`].
pub struct IncrementalClassifier {
    clauses: Vec<StoredClause>,
    next_id: ClauseId,
    revision: u64,
    backend: BackendState,
    concepts: BTreeSet<String>,
}

impl IncrementalClassifier {
    pub fn new(clauses: Vec<JClause>) -> Result<Self, IncrementalReasoningError> {
        let next_id = ClauseId::try_from(clauses.len())
            .ok()
            .and_then(|n| n.checked_add(1))
            .ok_or(IncrementalReasoningError::ClauseIdExhausted)?;
        let backend = build_backend(&clauses)?;
        let concepts = concept_signature(&clauses);
        let clauses = clauses
            .into_iter()
            .enumerate()
            .map(|(index, clause)| StoredClause {
                id: index as ClauseId + 1,
                clause,
            })
            .collect();
        Ok(IncrementalClassifier {
            clauses,
            next_id,
            revision: 0,
            backend,
            concepts,
        })
    }

    /// Atomically add normalised clauses. Pure-EL additions use the completion
    /// delta engine; CB additions resume a retained context-calculus fixpoint
    /// whenever its ordering/nominal preflight proves reuse safe. Other cases
    /// take the visible exact-rebuild path.
    pub fn add_clauses(
        &mut self,
        additions: Vec<JClause>,
    ) -> Result<IncrementalChange, IncrementalReasoningError> {
        let backend_before = self.backend.kind();
        if additions.is_empty() {
            return Ok(self.no_op_change(backend_before));
        }
        let ids = self.allocate_ids(additions.len())?;

        if let BackendState::El(classifier) = &mut self.backend {
            if let Ok(update) = classifier.add_clauses(additions.clone()) {
                self.commit_additions(ids.clone(), additions);
                self.revision += 1;
                self.concepts = concept_signature_from_store(&self.clauses);
                return Ok(IncrementalChange {
                    revision: self.revision,
                    added_clauses: ids.len(),
                    removed_clauses: 0,
                    total_clauses: self.clauses.len(),
                    added_clause_ids: ids,
                    removed_clause_ids: Vec::new(),
                    backend_before,
                    backend_after: IncrementalBackend::El,
                    strategy: if update.reused_fixpoint {
                        ChangeStrategy::ElDelta
                    } else {
                        ChangeStrategy::ExactRebuild
                    },
                    reused_fixpoint: update.reused_fixpoint,
                    reused_subsumptions: update.reused_subsumptions,
                    reused_edges: update.reused_edges,
                    new_subsumptions: update.new_subsumptions,
                    new_edges: update.new_edges,
                });
            }
        }

        let old_pairs = self.backend.pair_count();
        let retained = match &mut self.backend {
            BackendState::Cb(state) => match state.add_retained(&additions) {
                Some(update) => match update {
                    Ok(stats) => Some(stats),
                    Err(RetainedCbBoundary::UnsupportedClauses { dropped }) => {
                        return Err(IncrementalReasoningError::UnsupportedClauses { dropped });
                    }
                    Err(RetainedCbBoundary::IncompleteFixpoint) => {
                        // The live engine was not mutated. A fresh engine below
                        // may still complete under a smaller context graph.
                        None
                    }
                    Err(
                        RetainedCbBoundary::OrderingRouterChanged | RetainedCbBoundary::Engine(_),
                    ) => None,
                },
                None => None,
            },
            BackendState::El(_) => None,
        };
        if let Some(stats) = retained {
            let new_pairs = self.backend.pair_count();
            self.commit_additions(ids.clone(), additions);
            self.revision += 1;
            self.concepts = concept_signature_from_store(&self.clauses);
            return Ok(IncrementalChange {
                revision: self.revision,
                added_clauses: ids.len(),
                removed_clauses: 0,
                total_clauses: self.clauses.len(),
                added_clause_ids: ids,
                removed_clause_ids: Vec::new(),
                backend_before,
                backend_after: IncrementalBackend::Cb,
                strategy: ChangeStrategy::CbDelta,
                reused_fixpoint: true,
                reused_subsumptions: old_pairs.min(new_pairs),
                reused_edges: stats.edges_before,
                new_subsumptions: new_pairs.saturating_sub(old_pairs),
                new_edges: stats.edges_after.saturating_sub(stats.edges_before),
            });
        }

        let mut candidate = self.clause_snapshot();
        candidate.extend(additions.iter().cloned());
        let next_backend = build_backend(&candidate)?;
        let new_subsumptions = next_backend.pair_count();
        let backend_after = next_backend.kind();
        self.commit_additions(ids.clone(), additions);
        self.backend = next_backend;
        self.concepts = concept_signature(&candidate);
        self.revision += 1;
        Ok(IncrementalChange {
            revision: self.revision,
            added_clauses: ids.len(),
            removed_clauses: 0,
            total_clauses: self.clauses.len(),
            added_clause_ids: ids,
            removed_clause_ids: Vec::new(),
            backend_before,
            backend_after,
            strategy: ChangeStrategy::ExactRebuild,
            reused_fixpoint: false,
            reused_subsumptions: 0,
            reused_edges: 0,
            new_subsumptions,
            new_edges: 0,
        })
    }

    /// Atomically remove clauses by stable id. All removals rebuild exactly;
    /// removed ids are never reused by later additions.
    pub fn remove_clauses(
        &mut self,
        requested: &[ClauseId],
    ) -> Result<IncrementalChange, IncrementalReasoningError> {
        self.apply_change(requested, Vec::new())
    }

    /// Atomically remove and add clauses in one revision. A replacement never
    /// publishes the state between its deletion and addition halves.
    pub fn apply_change(
        &mut self,
        requested: &[ClauseId],
        additions: Vec<JClause>,
    ) -> Result<IncrementalChange, IncrementalReasoningError> {
        let backend_before = self.backend.kind();
        if requested.is_empty() {
            return self.add_clauses(additions);
        }

        let seen = self.validate_removals(requested)?;
        let added_ids = self.allocate_ids(additions.len())?;

        let mut candidate: Vec<JClause> = self
            .clauses
            .iter()
            .filter(|stored| !seen.contains(&stored.id))
            .map(|stored| stored.clause.clone())
            .collect();
        candidate.extend(additions.iter().cloned());
        let next_backend = build_backend(&candidate)?;
        let new_subsumptions = next_backend.pair_count();
        let backend_after = next_backend.kind();
        self.clauses.retain(|stored| !seen.contains(&stored.id));
        self.commit_additions(added_ids.clone(), additions);
        self.backend = next_backend;
        self.concepts = concept_signature(&candidate);
        self.revision += 1;
        Ok(IncrementalChange {
            revision: self.revision,
            added_clauses: added_ids.len(),
            removed_clauses: seen.len(),
            total_clauses: self.clauses.len(),
            added_clause_ids: added_ids,
            removed_clause_ids: seen.into_iter().collect(),
            backend_before,
            backend_after,
            strategy: ChangeStrategy::ExactRebuild,
            reused_fixpoint: false,
            reused_subsumptions: 0,
            reused_edges: 0,
            new_subsumptions,
            new_edges: 0,
        })
    }

    pub fn result(&self) -> IncrementalResult {
        self.backend.result()
    }

    pub fn is_subsumed_by(&self, sub: &str, sup: &str) -> Option<bool> {
        if let BackendState::El(classifier) = &self.backend {
            return classifier.is_subsumed_by(sub, sup);
        }
        let result = if let BackendState::Cb(state) = &self.backend {
            state.result_ref()
        } else {
            unreachable!("EL backend returned above")
        };
        if !self.concepts.contains(sub) {
            return None;
        }
        if result.inconsistent || sub == sup || is_top(sup) {
            return Some(true);
        }
        if !is_bottom(sup) && !self.concepts.contains(sup) {
            return Some(false);
        }
        let reported = if is_bottom(sup) { "owl:Nothing" } else { sup };
        Some(
            result
                .subsumptions
                .get(sub)
                .is_some_and(|supers| supers.iter().any(|candidate| candidate == reported)),
        )
    }

    pub fn is_inconsistent(&self) -> bool {
        self.backend.inconsistent()
    }

    pub fn backend(&self) -> IncrementalBackend {
        self.backend.kind()
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }

    pub fn clause_count(&self) -> usize {
        self.clauses.len()
    }

    pub fn clause_ids(&self) -> Vec<ClauseId> {
        self.clauses.iter().map(|stored| stored.id).collect()
    }

    fn no_op_change(&self, backend: IncrementalBackend) -> IncrementalChange {
        IncrementalChange {
            revision: self.revision,
            added_clauses: 0,
            removed_clauses: 0,
            total_clauses: self.clauses.len(),
            added_clause_ids: Vec::new(),
            removed_clause_ids: Vec::new(),
            backend_before: backend,
            backend_after: backend,
            strategy: ChangeStrategy::NoOp,
            reused_fixpoint: true,
            reused_subsumptions: 0,
            reused_edges: 0,
            new_subsumptions: 0,
            new_edges: 0,
        }
    }

    fn allocate_ids(&self, count: usize) -> Result<Vec<ClauseId>, IncrementalReasoningError> {
        let count =
            ClauseId::try_from(count).map_err(|_| IncrementalReasoningError::ClauseIdExhausted)?;
        let end = self
            .next_id
            .checked_add(count)
            .ok_or(IncrementalReasoningError::ClauseIdExhausted)?;
        Ok((self.next_id..end).collect())
    }

    fn validate_removals(
        &self,
        requested: &[ClauseId],
    ) -> Result<BTreeSet<ClauseId>, IncrementalReasoningError> {
        let mut seen = BTreeSet::new();
        let mut duplicates = BTreeSet::new();
        for &id in requested {
            if !seen.insert(id) {
                duplicates.insert(id);
            }
        }
        if !duplicates.is_empty() {
            return Err(IncrementalReasoningError::DuplicateClauseIds {
                ids: duplicates.into_iter().collect(),
            });
        }
        let known: BTreeSet<ClauseId> = self.clauses.iter().map(|stored| stored.id).collect();
        let unknown: Vec<ClauseId> = seen.difference(&known).copied().collect();
        if !unknown.is_empty() {
            return Err(IncrementalReasoningError::UnknownClauseIds { ids: unknown });
        }
        Ok(seen)
    }

    fn commit_additions(&mut self, ids: Vec<ClauseId>, additions: Vec<JClause>) {
        debug_assert_eq!(ids.len(), additions.len());
        for (id, clause) in ids.iter().copied().zip(additions) {
            self.clauses.push(StoredClause { id, clause });
        }
        self.next_id = ids.last().map_or(self.next_id, |id| *id + 1);
    }

    fn clause_snapshot(&self) -> Vec<JClause> {
        self.clauses
            .iter()
            .map(|stored| stored.clause.clone())
            .collect()
    }
}

/// Classify a snapshot with the same EL-first, exact-CB-fallback policy used by
/// [`IncrementalClassifier`].
pub fn classify_fresh(
    clauses: &[JClause],
) -> Result<(IncrementalBackend, IncrementalResult), IncrementalReasoningError> {
    let backend = build_backend(clauses)?;
    Ok((backend.kind(), backend.result()))
}

/// Run a fresh consequence-based classification and reject every incomplete
/// outcome. This is also the exact-rebuild oracle for differential tests.
pub fn classify_cb_fresh(
    clauses: &[JClause],
) -> Result<IncrementalResult, IncrementalReasoningError> {
    let mut reasoner = Reasoner::new(clauses);
    let dropped = reasoner.dropped_unsupported();
    if dropped != 0 {
        return Err(IncrementalReasoningError::UnsupportedClauses { dropped });
    }
    reasoner.saturate();
    if reasoner.incomplete() {
        return Err(IncrementalReasoningError::IncompleteFixpoint);
    }
    let inconsistent = reasoner.inconsistent();
    let subsumptions = reasoner
        .take_subsumptions()
        .into_iter()
        .map(|(subject, supers)| (subject, supers.into_iter().collect()))
        .collect();
    Ok(IncrementalResult {
        subsumptions,
        inconsistent,
        dropped: 0,
        unresolved: Vec::new(),
    })
}

fn build_backend(clauses: &[JClause]) -> Result<BackendState, IncrementalReasoningError> {
    if let Ok(classifier) = IncrementalElClassifier::new(clauses.to_vec()) {
        return Ok(BackendState::El(classifier));
    }
    if RetainedCbReasoner::available_for_current_route() {
        let reasoner = RetainedCbReasoner::new(clauses);
        let dropped = reasoner.dropped_unsupported();
        if dropped != 0 {
            return Err(IncrementalReasoningError::UnsupportedClauses { dropped });
        }
        if reasoner.incomplete() {
            return Err(IncrementalReasoningError::IncompleteFixpoint);
        }
        let result = result_from_retained_cb(&reasoner);
        return Ok(BackendState::Cb(CbBackendState::Retained {
            reasoner,
            result,
        }));
    }
    classify_cb_fresh(clauses)
        .map(CbBackendState::Snapshot)
        .map(BackendState::Cb)
}

fn result_from_retained_cb(reasoner: &RetainedCbReasoner) -> IncrementalResult {
    IncrementalResult {
        subsumptions: reasoner.subsumptions().into_iter().collect(),
        inconsistent: reasoner.inconsistent(),
        dropped: 0,
        unresolved: Vec::new(),
    }
}

fn concept_signature(clauses: &[JClause]) -> BTreeSet<String> {
    clauses
        .iter()
        .flat_map(|clause| clause.body.iter().chain(&clause.head))
        .filter_map(|atom| match atom {
            JAtom::Concept { concept, .. } => Some(concept.clone()),
            _ => None,
        })
        .collect()
}

fn concept_signature_from_store(clauses: &[StoredClause]) -> BTreeSet<String> {
    clauses
        .iter()
        .flat_map(|stored| stored.clause.body.iter().chain(&stored.clause.head))
        .filter_map(|atom| match atom {
            JAtom::Concept { concept, .. } => Some(concept.clone()),
            _ => None,
        })
        .collect()
}

fn is_top(name: &str) -> bool {
    name == "owl:Thing" || name == "http://www.w3.org/2002/07/owl#Thing" || name == "\u{22a4}"
}

fn is_bottom(name: &str) -> bool {
    name == "owl:Nothing" || name == "http://www.w3.org/2002/07/owl#Nothing" || name == "\u{22a5}"
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum Command {
    /// Start or replace the current session at revision 0.
    Init {
        clauses: Vec<JClause>,
    },
    /// Atomically add normalised clauses to the current session.
    Add {
        clauses: Vec<JClause>,
    },
    /// Atomically remove clauses by the ids returned by init/add.
    Remove {
        clause_ids: Vec<ClauseId>,
    },
    /// Atomically remove and add clauses in one revision.
    Change {
        #[serde(default)]
        remove_clause_ids: Vec<ClauseId>,
        #[serde(default)]
        add_clauses: Vec<JClause>,
    },
    Classify,
    IsSubsumedBy {
        sub: String,
        sup: String,
    },
    Stats,
}

/// Serve one incremental classifier over newline-delimited JSON.
///
/// Command errors are returned as JSON records and do not terminate the
/// stream. A rejected init/add/remove/change leaves any preceding session
/// live. Only transport I/O errors are returned from this function.
pub fn run_jsonl_session<R: BufRead, W: Write>(reader: R, mut writer: W) -> std::io::Result<()> {
    let mut session: Option<IncrementalClassifier> = None;
    for line in reader.lines() {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let response = match serde_json::from_str::<Command>(&line) {
            Ok(command) => handle(command, &mut session),
            Err(error) => error_response("parse", error.to_string()),
        };
        serde_json::to_writer(&mut writer, &response)
            .map_err(|error| std::io::Error::new(std::io::ErrorKind::InvalidData, error))?;
        writer.write_all(b"\n")?;
        writer.flush()?;
    }
    Ok(())
}

fn handle(command: Command, session: &mut Option<IncrementalClassifier>) -> Value {
    match command {
        Command::Init { clauses } => match IncrementalClassifier::new(clauses) {
            Ok(classifier) => {
                let response = json!({
                    "status": "ok",
                    "op": "init",
                    "revision": classifier.revision(),
                    "total_clauses": classifier.clause_count(),
                    "clause_ids": classifier.clause_ids(),
                    "backend": classifier.backend(),
                    "inconsistent": classifier.is_inconsistent(),
                });
                *session = Some(classifier);
                response
            }
            Err(error) => error_response("init", error.to_string()),
        },
        Command::Add { clauses } => match session.as_mut() {
            Some(classifier) => match classifier.add_clauses(clauses) {
                Ok(update) => json!({
                    "status": "ok",
                    "op": "add",
                    "update": update,
                    "inconsistent": classifier.is_inconsistent(),
                }),
                Err(error) => error_response("add", error.to_string()),
            },
            None => no_session("add"),
        },
        Command::Remove { clause_ids } => match session.as_mut() {
            Some(classifier) => match classifier.remove_clauses(&clause_ids) {
                Ok(update) => json!({
                    "status": "ok",
                    "op": "remove",
                    "update": update,
                    "inconsistent": classifier.is_inconsistent(),
                }),
                Err(error) => error_response("remove", error.to_string()),
            },
            None => no_session("remove"),
        },
        Command::Change {
            remove_clause_ids,
            add_clauses,
        } => match session.as_mut() {
            Some(classifier) => match classifier.apply_change(&remove_clause_ids, add_clauses) {
                Ok(update) => json!({
                    "status": "ok",
                    "op": "change",
                    "update": update,
                    "inconsistent": classifier.is_inconsistent(),
                }),
                Err(error) => error_response("change", error.to_string()),
            },
            None => no_session("change"),
        },
        Command::Classify => match session.as_ref() {
            Some(classifier) => json!({
                "status": "ok",
                "op": "classify",
                "revision": classifier.revision(),
                "backend": classifier.backend(),
                "result": classifier.result(),
            }),
            None => no_session("classify"),
        },
        Command::IsSubsumedBy { sub, sup } => match session.as_ref() {
            Some(classifier) => {
                let entailed = classifier.is_subsumed_by(&sub, &sup);
                json!({
                    "status": "ok",
                    "op": "is_subsumed_by",
                    "revision": classifier.revision(),
                    "backend": classifier.backend(),
                    "sub": sub,
                    "sup": sup,
                    "entailed": entailed,
                })
            }
            None => no_session("is_subsumed_by"),
        },
        Command::Stats => match session.as_ref() {
            Some(classifier) => json!({
                "status": "ok",
                "op": "stats",
                "revision": classifier.revision(),
                "total_clauses": classifier.clause_count(),
                "clause_ids": classifier.clause_ids(),
                "backend": classifier.backend(),
                "inconsistent": classifier.is_inconsistent(),
            }),
            None => no_session("stats"),
        },
    }
}

fn no_session(op: &str) -> Value {
    error_response(op, "session is not initialised; send an init command first")
}

fn error_response(op: &str, message: impl Into<String>) -> Value {
    json!({
        "status": "error",
        "op": op,
        "error": message.into(),
    })
}
