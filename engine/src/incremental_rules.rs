//! Retained source-level adapter for the DL-safe-rules route.
//!
//! DL-safe rules range only over named individuals, so they can change KB
//! consistency but not the TBox class hierarchy.  We retain that taxonomy
//! while the normalized non-ground TBox and public class signature stay
//! byte-for-byte equal, and update only the typed rule/ABox consistency probe.

use std::collections::{HashMap, HashSet};

use crate::frontend::FrontendResult;
use crate::json_io::{JAtom, JClause, JRule, JTerm};
use crate::orchestrate::{cb_to_ht, Classification};

pub(crate) struct IncrementalRulesClassifier {
    tbox_clauses: HashMap<JClause, usize>,
    ground_clauses: HashMap<JClause, usize>,
    rules: HashMap<JRule, usize>,
    named: Vec<String>,
    iri_map: std::collections::BTreeMap<String, String>,
    rbox: Vec<Vec<String>>,
    cardinalities: Vec<crate::json_io::CardMeta>,
    definers: Vec<crate::json_io::DefinerMeta>,
    source_axioms: Vec<crate::json_io::SourceAxiomMeta>,
    classification: Classification,
    /// Last complete TBox taxonomy. The public inconsistent answer is empty,
    /// but retaining this independent result lets an ABox/rule removal restore
    /// consistency without rebuilding unchanged terminology.
    retained_taxonomy: Option<Classification>,
}

pub(crate) struct RuleUpdate {
    pub classification: Classification,
    pub reused_subsumptions: usize,
    pub probe_reused: bool,
    pub retained_taxonomy: Option<Classification>,
}

impl IncrementalRulesClassifier {
    pub(crate) fn new(frontend: &FrontendResult, classification: Classification) -> Self {
        let retained_taxonomy = classification.consistent.then(|| classification.clone());
        Self::with_taxonomy(frontend, classification, retained_taxonomy)
    }

    pub(crate) fn with_taxonomy(
        frontend: &FrontendResult,
        classification: Classification,
        retained_taxonomy: Option<Classification>,
    ) -> Self {
        IncrementalRulesClassifier {
            tbox_clauses: tbox_multiset(&frontend.clauses),
            ground_clauses: ground_multiset(&frontend.clauses),
            rules: rule_multiset(&frontend.rules),
            named: frontend.named.clone(),
            iri_map: frontend.iri_map.clone(),
            rbox: frontend.rbox.clone(),
            cardinalities: frontend.cardinalities.clone(),
            definers: frontend.definers.clone(),
            source_axioms: frontend.source_axioms.clone(),
            classification,
            retained_taxonomy,
        }
    }

    /// Return `None` when a TBox/signature change requires the ordinary exact
    /// route. The live state is immutable until the caller commits this value.
    pub(crate) fn updated(&self, candidate: &FrontendResult) -> Result<Option<RuleUpdate>, String> {
        if candidate.route != "ht_rules"
            || self.tbox_clauses != tbox_multiset(&candidate.clauses)
            || self.named != candidate.named
            || self.iri_map != candidate.iri_map
            || self.rbox != candidate.rbox
            || self.cardinalities != candidate.cardinalities
            || self.definers != candidate.definers
            || self.source_axioms != candidate.source_axioms
        {
            return Ok(None);
        }

        let old_consistent = self.classification.consistent;
        // Removing constraints from a model preserves that model. Detect the
        // common pure-removal case without launching another search.
        let candidate_ground = ground_multiset(&candidate.clauses);
        let candidate_rules = rule_multiset(&candidate.rules);
        let pure_removal = multiset_subset(&candidate_ground, &self.ground_clauses)
            && multiset_subset(&candidate_rules, &self.rules);
        let (consistent, probe_reused) = if old_consistent && pure_removal {
            (true, true)
        } else if !old_consistent
            && multiset_subset(&self.ground_clauses, &candidate_ground)
            && multiset_subset(&self.rules, &candidate_rules)
        {
            // Inconsistency is monotone under additions.
            (false, true)
        } else {
            (rules_consistent(candidate)?, false)
        };

        let mut classification = if old_consistent {
            self.classification.clone()
        } else if consistent {
            match self.retained_taxonomy.clone() {
                Some(taxonomy) => taxonomy,
                None => return Ok(None),
            }
        } else {
            self.classification.clone()
        };
        classification.consistent = consistent;
        if !consistent {
            classification.subsumptions.clear();
            classification.unsatisfiable.clear();
        }
        let retained_taxonomy = if consistent {
            Some(classification.clone())
        } else {
            self.retained_taxonomy
                .clone()
                .or_else(|| old_consistent.then(|| self.classification.clone()))
        };
        Ok(Some(RuleUpdate {
            reused_subsumptions: classification.subsumptions.len(),
            classification,
            probe_reused,
            retained_taxonomy,
        }))
    }
}

fn term_is_ground(term: &JTerm) -> bool {
    match term {
        JTerm::Ind { .. } | JTerm::Aux { .. } => true,
        JTerm::Fun { arg, .. } => term_is_ground(arg),
        JTerm::Var { .. } => false,
    }
}

fn clause_is_ground(clause: &JClause) -> bool {
    clause
        .body
        .iter()
        .chain(&clause.head)
        .any(|atom| match atom {
            JAtom::Concept { term, .. } => term_is_ground(term),
            JAtom::Role { source, target, .. } => term_is_ground(source) || term_is_ground(target),
            JAtom::Eq { left, right } => term_is_ground(left) || term_is_ground(right),
        })
}

fn multiset<'a>(clauses: impl Iterator<Item = &'a JClause>) -> HashMap<JClause, usize> {
    let mut counts = HashMap::new();
    for clause in clauses {
        *counts.entry(clause.clone()).or_default() += 1;
    }
    counts
}

fn tbox_multiset(clauses: &[JClause]) -> HashMap<JClause, usize> {
    multiset(clauses.iter().filter(|clause| !clause_is_ground(clause)))
}

fn ground_multiset(clauses: &[JClause]) -> HashMap<JClause, usize> {
    multiset(clauses.iter().filter(|clause| clause_is_ground(clause)))
}

fn multiset_subset<T: Eq + std::hash::Hash>(
    left: &HashMap<T, usize>,
    right: &HashMap<T, usize>,
) -> bool {
    left.iter()
        .all(|(clause, count)| right.get(clause).copied().unwrap_or(0) >= *count)
}

fn rule_multiset(rules: &[JRule]) -> HashMap<JRule, usize> {
    let mut counts = HashMap::new();
    for rule in rules {
        *counts.entry(rule.clone()).or_default() += 1;
    }
    counts
}

fn rules_consistent(frontend: &FrontendResult) -> Result<bool, String> {
    let named: HashSet<String> = frontend.named.iter().cloned().collect();
    let tin = cb_to_ht::convert(
        &frontend.clauses,
        None,
        &named,
        &frontend.cardinalities,
        &frontend.definers,
        &frontend.source_axioms,
        false,
        &frontend.rules,
        true,
    );
    let input = serde_json::to_string(&tin).map_err(|error| error.to_string())?;
    let _environment = crate::routing::EnvironmentGuard::capture();
    std::env::set_var("KM_RULES_CONSISTENCY", "1");
    std::env::remove_var("KM_HT");
    let output = std::thread::Builder::new()
        .name("km-incremental-rules".into())
        .stack_size(4usize << 30)
        .spawn(move || crate::tableau::run_json(&input))
        .map_err(|error| error.to_string())?
        .join()
        .map_err(|_| "incremental rules probe panicked".to_string())??;
    let value: serde_json::Value =
        serde_json::from_str(&output).map_err(|error| error.to_string())?;
    value["consistent"]
        .as_bool()
        .ok_or_else(|| "rules probe omitted consistency verdict".to_string())
}
