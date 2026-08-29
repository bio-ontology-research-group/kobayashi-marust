//! Retained typed positive-ABox completion for the automatic ELC route.
//!
//! The batch route translates named individuals into fresh EL completion
//! roots and proves both consistency and the unchanged named TBox taxonomy in
//! one fixpoint. This adapter retains that exact translated fixpoint. Pure
//! additions use ordinary EL replay; removals and replacements use EL's
//! dependency-component retraction.

use std::collections::{HashMap, VecDeque};

use crate::elcomplete::{
    prepare_positive_abox, ElResult, IncrementalElClassifier, IncrementalUpdate,
    PositiveAboxPreparation,
};
use crate::frontend::FrontendResult;
use crate::json_io::JClause;

pub(crate) struct IncrementalPositiveAboxClassifier {
    classifier: IncrementalElClassifier,
    augmented_clauses: Vec<JClause>,
    roots: std::collections::HashSet<String>,
}

pub(crate) struct PositiveAboxUpdate {
    pub result: ElResult,
    pub consistent: bool,
    pub stats: IncrementalUpdate,
}

impl IncrementalPositiveAboxClassifier {
    pub(crate) fn new(frontend: &FrontendResult) -> Option<(Self, ElResult, bool)> {
        if frontend.nominal_abox.individuals.is_empty() {
            return None;
        }
        let PositiveAboxPreparation::Clauses { clauses, roots } =
            prepare_positive_abox(frontend.clauses.clone(), &frontend.nominal_abox)?
        else {
            return None;
        };
        let classifier = IncrementalElClassifier::new(clauses.clone()).ok()?;
        let result = classifier.result();
        let consistent = positive_result_consistent(&result, &roots);
        Some((
            IncrementalPositiveAboxClassifier {
                classifier,
                augmented_clauses: clauses,
                roots,
            },
            result,
            consistent,
        ))
    }

    /// The live classifier changes only after the complete candidate typed
    /// translation has passed all frontend and EL-fragment checks.
    pub(crate) fn update(
        &mut self,
        candidate: &FrontendResult,
    ) -> Result<Option<PositiveAboxUpdate>, String> {
        if candidate.route != "elc" {
            return Ok(None);
        }
        let Some(prepared) =
            prepare_positive_abox(candidate.clauses.clone(), &candidate.nominal_abox)
        else {
            return Ok(None);
        };
        let PositiveAboxPreparation::Clauses { clauses, roots } = prepared else {
            return Ok(None);
        };
        let (removed, additions) = clause_delta(&self.augmented_clauses, &clauses);
        let stats = if removed.is_empty() {
            self.classifier
                .add_clauses(additions)
                .map_err(|error| error.to_string())?
        } else {
            let mut changed = removed;
            changed.extend(additions);
            let (next, stats) = self
                .classifier
                .replace_clauses(clauses.clone(), &changed)
                .map_err(|error| error.to_string())?;
            self.classifier = next;
            stats
        };
        self.augmented_clauses = clauses;
        self.roots = roots;
        let result = self.classifier.result();
        let consistent = positive_result_consistent(&result, &self.roots);
        Ok(Some(PositiveAboxUpdate {
            result,
            consistent,
            stats,
        }))
    }
}

fn positive_result_consistent(
    result: &ElResult,
    roots: &std::collections::HashSet<String>,
) -> bool {
    !result.inconsistent
        && !roots.iter().any(|root| {
            result
                .subsumptions
                .get(root)
                .is_some_and(|supers| supers.iter().any(|sup| sup == "owl:Nothing"))
        })
}

/// Duplicate-preserving delta. The returned first vector contains removed
/// clause values because the EL dependency graph needs their symbols.
fn clause_delta(old: &[JClause], new: &[JClause]) -> (Vec<JClause>, Vec<JClause>) {
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
    let removed = old
        .iter()
        .enumerate()
        .filter_map(|(index, clause)| (!used[index]).then(|| clause.clone()))
        .collect();
    (removed, additions)
}
