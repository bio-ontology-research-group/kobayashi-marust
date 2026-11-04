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
//! Two further port deviations meet the same cache: the existential test
//! read only the role reapply queue (`label_restricts_role_cardinality`),
//! and the replay of an entry skipped the AND rule
//! (`expanded_concept_skip_function`).
//!
//! `KM_HT_SATEXP_ABSORB_LEGACY=1` restores the port's former behaviour for
//! all of them (negative control); production never sets it.

use super::super::model::op::{CCATLEAST, CCATMOST, CCBOTTOM, CCNOMINAL, CCTOP};
use super::super::model::ontology::OntologyArenas;
use super::super::model::substrate::{Cint64, NegLink};
use super::super::model::{ConceptId, RoleId};
use super::super::process::context::ProcessContext;
use super::super::process::{ConDescId, NodeId};

/// `KM_HT_SATEXP_ABSORB_LEGACY` (diagnostic): `1` or `all` restores every
/// arm; a comma list of `functional`, `top`, `value`, `label`, `replay`
/// restores those arms (`top`: the `⊤` qualifier of `atmost_is_functional_rule`).
fn satexp_absorb_legacy_arm(arm: &str) -> bool {
    static ARMS: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
    match ARMS.get_or_init(|| std::env::var("KM_HT_SATEXP_ABSORB_LEGACY").ok()) {
        None => false,
        Some(v) => v == "1" || v == "all" || v.split(',').any(|a| a.trim() == arm),
    }
}

/// `true` when the at-most concept `concept` (negated: `¬≥n`) is Konclude's
/// functional `≤1 R`, which `applyATMOSTRule` sends to `applyFUNCTIONALRule`
/// (cpp 14924, 14933) and so never absorbs on a satisfiable-cached node:
/// cardinality 1 and no qualifier operand. A `⊤` qualifier counts as none:
/// Konclude's builder drops it (`CConcreteOntologyUpdateBuilder.cpp`
/// 1197-1199), while the bridge keeps it for `≤1 R` written with `owl:Thing`
/// (`SubClassOf(owl:Thing ObjectMaxCardinality(1 :r))`, seeds `nn1348min`,
/// `nn1116`). The bridge's concept stays as it is; only its absorption
/// follows Konclude's functional rule.
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
    if cardinality != 1 {
        return false;
    }
    match c.get_operand_list() {
        [] => true,
        [only] if !satexp_absorb_legacy_arm("top") => {
            let code = onto.concept(only.target).get_operator_code();
            (code == CCTOP && !only.negated) || (code == CCBOTTOM && only.negated)
        }
        _ => false,
    }
}

/// The cached-ancestor blocks that a successor created for a VALUE-shortcut
/// existential does not inherit: Konclude creates no successor there (it
/// links the node to the nominal), so nothing between the node and the
/// nominal is ever blocked by the node's cache status. Clearing a block only
/// lets the successor be processed (its nominal concept merges it into the
/// nominal), so it cannot change a correct verdict.
pub(crate) const VALUE_SHORTCUT_CLEARED_ANCESTOR_FLAGS: Cint64 =
    super::super::process::node::IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED
        | super::super::process::node::IndividualProcessNode::PRF_ANCESTORSIGNATUREBLOCKINGCACHED
        | super::super::process::node::IndividualProcessNode::PRF_ANCESTORSATURATIONBLOCKINGCACHED;

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

/// `true` when the label of `node` holds a cardinality restriction on `role`
/// (`≤n role.C`, or `¬≥n role.C`), processed or still queued.
///
/// `isGeneratingConceptSatisfiableCachedAbsorpable` (cpp 14217-14253) refuses
/// to absorb `∃R.C` on a satisfiable-cached node whose link to its ancestor
/// carries a super role `S` of `R` with an at-most or at-least restriction in
/// the node's role reapply queue. A restriction enters that queue when its
/// rule runs, so the test depends on the order in which the node's queue
/// pops the existential and the restriction. Konclude gives an unqualified
/// `≤1 S` priority 5.5, above `∃` (4), so that restriction is registered
/// first; a qualified `≤n S.C` has priority 3 plus an offset, below `∃`, and
/// is not. The port reaches the second case for every `≤1 S.⊤` the bridge
/// builds with a `⊤` operand (`SubClassOf(owl:Thing ObjectMaxCardinality(1 :r))`,
/// seed `nn1348min`), where Konclude's builder drops the operand. Reading
/// the label as well makes the refusal independent of the queue order. It
/// can only refuse more absorptions, which runs the ordinary rule
/// (docs/HYBRID-CB-HT.md section 23); `KM_HT_SATEXP_ABSORB_LEGACY=label`
/// restores the reapply-queue-only test.
pub(crate) fn label_restricts_role_cardinality(
    pc: &ProcessContext,
    onto: &OntologyArenas,
    node: NodeId,
    role: RoleId,
) -> bool {
    if satexp_absorb_legacy_arm("label") || node.is_none() {
        return false;
    }
    let ls = pc.node(node).use_reapply_con_label_set;
    if ls.is_none() {
        return false;
    }
    let mut it = pc.label_set(ls).get_concept_label_set_iterator(true, false, false);
    while it.has_next() {
        let cd: ConDescId = it.next(true, pc);
        if cd.is_none() {
            break;
        }
        let des = pc.con_desc(cd);
        let concept = onto.concept(des.get_concept());
        let code = concept.get_operator_code();
        if ((code == CCATMOST && !des.is_negated()) || (code == CCATLEAST && des.is_negated()))
            && concept.get_role() == role
        {
            return true;
        }
    }
    false
}
