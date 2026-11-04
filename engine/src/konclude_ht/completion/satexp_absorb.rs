//! Satisfiable-cached absorption of generating and merging concepts
//! (docs/HYBRID-CB-HT.md section 23).
//!
//! A node that the satisfiable expander cache marks `PRF_SATISFIABLECACHED`
//! keeps running its own rules; Konclude only defers two kinds of concepts on
//! it, recording them for a later reapplication if the cache status is lost:
//!
//! * a generating concept (`∃`, `≥n`) whose successor the cache entry stands
//!   for (`applySOMERule`, cpp 14388-14393, guarded by
//!   `isGeneratingConceptSatisfiableCachedAbsorpable`, cpp 14217-14253);
//! * a merging at-most restriction (`applyATMOSTRule`, cpp 14938-14941).
//!
//! Two of Konclude's rule paths reach neither absorption, and the port took
//! both into it:
//!
//! 1. An unqualified `≤1 R` goes to `applyFUNCTIONALRule` (cpp 14933-14935)
//!    before the at-most absorption test, so it is never absorbed: it merges
//!    the node's `R`-neighbours and registers itself in the node's role
//!    reapply queue (cpp 14868-14871), which is what
//!    `isGeneratingConceptSatisfiableCachedAbsorpable` later reads to refuse
//!    absorbing an `∃R.C` whose successor would have to be merged into the
//!    ancestor.
//! 2. An `∃R.{a}` with a single positive nominal operand is answered by the
//!    VALUE shortcut of `applySOMERule` (cpp 14316-14380), which links the
//!    node to the nominal and returns before the absorption test.
//!
//! `KM_HT_SATEXP_ABSORB_LEGACY=1` restores the port's former behaviour for
//! both, and the `⊤` operand of `filler_is_top` (negative control);
//! production never sets it.

use super::super::model::op::{CCNOMINAL, CCTOP, CCBOTTOM};
use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Cint64, NegLink};
use super::super::model::ConceptId;

/// `KM_HT_SATEXP_ABSORB_LEGACY` (diagnostic): `1` or `all` restores every
/// arm; a comma list of `functional`, `value`, `top`, `replay` restores those
/// arms.
fn satexp_absorb_legacy_arm(arm: &str) -> bool {
    static ARMS: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    match ARMS.get_or_init(|| std::env::var("KM_HT_SATEXP_ABSORB_LEGACY").ok()) {
        None => false,
        Some(v) => v == "1" || v == "all" || v.split(',').any(|a| a.trim() == arm),
    }
}

/// `true` when the at-most concept `concept` (negated: `¬≥n`) is dispatched to
/// Konclude's `applyFUNCTIONALRule` and so is never absorbed on a
/// satisfiable-cached node: cardinality 1 and no qualifier operand
/// (cpp 14924, 14933).
pub(crate) fn atmost_is_functional_rule(
    onto: &OntologyArenas,
    concept: ConceptId,
    negate: bool,
) -> bool {
    if satexp_absorb_legacy_arm("functional") {
        return false;
    }
    let c = onto.concept(concept);
    let cardinality: Cint64 = c.get_parameter() - Cint64::from(negate);
    cardinality == 1 && c.get_operand_list().is_empty()
}

/// `true` when an `∃` (or `≥1`) with these operands is answered by Konclude's
/// VALUE shortcut in `applySOMERule` and so never reaches the
/// satisfiable-cached absorption: one operand, positive after `negate`, whose
/// operator is `CCNOMINAL` (cpp 14316-14318; the saturation-integrated
/// nominal arm needs a saturation node with an integrated nominal, which the
/// port does not consult here, so that arm keeps the absorption test).
pub(crate) fn some_is_value_shortcut(
    onto: &OntologyArenas,
    operands: &[NegLink<ConceptId>],
    negate: bool,
) -> bool {
    if satexp_absorb_legacy_arm("value") || operands.len() != 1 {
        return false;
    }
    let operand = operands[0];
    !(operand.negated ^ negate) && onto.concept(operand.target).get_operator_code() == CCNOMINAL
}

/// `true` when `filler` is `⊤` (or `¬⊥`): Konclude's ontology builder gives a
/// cardinality restriction with the top class no operand at all
/// (`CConcreteOntologyUpdateBuilder.cpp` 1175-1177 and 1197-1199), which makes
/// `≤1 R.⊤` the functional `≤1 R` of point 1 above.
pub(crate) fn filler_is_top(onto: &OntologyArenas, filler: (ConceptId, bool)) -> bool {
    if satexp_absorb_legacy_arm("top") || filler.0.is_none() {
        return false;
    }
    let code = onto.concept(filler.0).get_operator_code();
    (code == CCTOP && !filler.1) || (code == CCBOTTOM && filler.1)
}

/// The skip function for a concept replayed from a satisfiable expander cache
/// entry (`expandCachedConcepts`, cpp 6482): Konclude passes `applyANDRule`,
/// because an entry is written only after direct rule preprocessing has
/// applied every AND-family concept (AND, SUB, EQ, TOP, IMPLTRIG,
/// BRANCHTRIG, priority 13, above the immediate-processing limit 8) to the
/// label, so their operands are in the entry and replayed with them. The
/// port runs most terminologies without direct rule preprocessing, so an
/// entry can be written while such a concept still waits in the queue (seen
/// on `m53tiny`: `{GO_0005518, Continuant}` expanded to `GO_0003674` before
/// `GO_0003674 ⊑ Function` was applied, and a later replay added
/// `GO_0003674` without its operand, hiding the clash with `¬Function`).
/// The replay therefore queues AND-family concepts as well; their rule only
/// re-adds operands, so this can cost a rule application, never an answer.
/// `KM_HT_SATEXP_ABSORB_LEGACY=replay` restores Konclude's skip.
pub(crate) fn expanded_concept_skip_function() -> super::algorithm::TableauRuleFunction {
    if satexp_absorb_legacy_arm("replay") {
        super::u04::TABLEAU_RULE_APPLY_AND
    } else {
        super::super::model::substrate::INVALID
    }
}
