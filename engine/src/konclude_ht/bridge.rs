//! # Bridge: `TInput` (cb_to_ht HtClauses) → `OntologyArenas`
//!
//! The production-route input builder for `konclude_ht` — maps KM's
//! reverse-Skolemized HT clause form (`orchestrate::cb_to_ht::TInput`, the
//! same input the fast Ht consumes) onto Konclude-style concept structures
//! (`CCATOM`/`CCIMPL`/`CCOR`/`CCALL`/`CCSOME` operand trees): exactly the
//! encoding `completion::classify_test`'s `Env` builds programmatically, so
//! everything the completion engine already runs (implication unfolding, the
//! OR rule + the sound same-node backtrack, ∃/∀ successor rules) applies
//! unchanged to bridged ontologies.
//!
//! KEPT OUT OF THE PRODUCTION CLASSIFY PATH until verdict parity vs the
//! existing engines is established across the corpus — the bridge and its
//! driver are only reachable from tests today (nothing in `orchestrate` calls
//! them). Coverage is v1-PARTIAL and every clause the encoder cannot express
//! is COUNTED in [`Bridged::unsupported`]; a caller must treat
//! `unsupported > 0` as "the bridged ontology is an UNDER-approximation" —
//! satisfiable verdicts are then not trustworthy (missing constraints), while
//! clash verdicts remain sound (all encoded concepts are faithful).
//!
//! v1 clause coverage (one implication concept per clause, seeded per pass by
//! the re-drive loop exactly like the classify_test GCI harness):
//!   - concept-only clauses over the clause root variable:
//!     `C1 ∧ … ∧ Cn → D1 ∨ … ∨ Dm`  ⇒  `CCIMPL[ head, ¬C1, …, ¬Cn ]` with
//!     `head = Dm | CCOR[D1..Dm] | CCBOTTOM` (heads may be `Exist` ⇒ `CCSOME`);
//!   - single-role-body clauses `…C(0)… ∧ R(0,1) ∧ …D(1)… → …E(0)… ∨ …F(1)…`
//!     ⇒  `CCIMPL[ CCOR[E…, CCALL(R, CCOR[¬D…, F…])], ¬C… ]`
//!     (the standard `∀`-form of a guarded two-variable clause);
//!   - everything else (multiple role atoms, head role atoms / role
//!     hierarchy, `Eq`, body `Exist`, nominals, card_defs, chains) counts as
//!     unsupported in v1.
use std::collections::{BTreeSet, HashMap};

use super::classifier::{
    OptimizedKPSetClassSubsumptionClassifierThread, RecordingClassificationMessageDataObserver,
    SynchronousKPSetClassState,
};
use super::completion::algorithm::CompletionTaskHandleAlgorithm;
use super::completion::context::CalculationAlgorithmContextBase;
use super::completion::stubs::SatisfiableTaskClassificationMessageAnalyser;
use super::model::concept::Concept;
use super::model::concept_process::{ConceptProcessData, ReplacementData};
use super::model::op;
use super::model::role::Role;
use super::model::role_chain::RoleChain;
use super::model::stubs::NameId;
use super::model::substrate::{Cint64, Id, NegLink, INVALID};
use super::model::{ConceptId, RoleId};
use super::preprocess::role_chain_automata::RoleChainAutomataTransformationPreProcess;
use super::process::descriptor::{
    ConceptDescriptor, ConceptProcessDescriptor, ConceptProcessPriority,
};
use super::process::node::IndividualProcessNode;
use super::process::queues::ConceptProcessingQueue;
use super::process::NodeId;
use super::task::adapters::{SatisfiableTaskClassificationMessageAdapter, EFEXTRACTALL};
use crate::json_io::DefinerKind;
use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};

type SourceConcept = crate::frontend::syntax::Concept;
type SourceRole = crate::frontend::syntax::Role;

/// The bridged terminology: arena ids for the TInput's named concepts/roles
/// plus the per-clause implication concepts the probe driver re-seeds.
pub struct Bridged {
    /// `named[i]` = the `CCATOM` concept for `TInput.concepts[i]`.
    pub named: Vec<ConceptId>,
    /// `roles[i]` = the arena role for `TInput.roles[i]`.
    pub roles: Vec<RoleId>,
    /// One implication (`CCIMPL`) concept per encoded clause — the TBox the
    /// driver seeds on every re-drive pass (the classify_test GCI harness
    /// pattern; stands in for the unported condensed reapply queue).
    pub tbox: Vec<ConceptId>,
    /// Clauses the v1 encoder could NOT express. `> 0` ⇒ the bridged ontology
    /// under-approximates the input: "satisfiable" verdicts are unreliable.
    pub unsupported: usize,
    /// Implications absorbed onto their first positive trigger concept
    /// (`CCATOM` host promoted to `CCSUB`; see the attachment pass) — these
    /// are unfolded only in nodes whose label contains the trigger.
    pub absorbed: usize,
    /// Implications with no positive concept trigger, attached to the
    /// ontology TOP concept (scanned by EVERY node).
    pub top_attached: usize,
    /// Singleton concepts (`C(x) ∧ C(y) → x = y` clause shape — datatype
    /// value identity): consumed by the kernel's deterministic
    /// scan-at-fixpoint merge; must be installed on every probe algorithm.
    pub singleton_concepts: Vec<ConceptId>,
    /// True when the terminology was built from normalized source axioms.
    /// Native CCSUB/trigger/range links reach queue fixpoint in one completion
    /// task and do not need the legacy clause re-drive repair.
    pub source_tbox: bool,
}

/// Tag base for bridged concepts (tag 1 is the ontology TOP sentinel).
const TAG_BASE: Cint64 = 10;

struct Builder<'a> {
    ctx: &'a mut CalculationAlgorithmContextBase,
    next_tag: Cint64,
}

impl<'a> Builder<'a> {
    fn fresh_tag(&mut self) -> Cint64 {
        let t = self.next_tag;
        self.next_tag += 1;
        t
    }
    fn atom(&mut self, tag: Cint64) -> ConceptId {
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// `CCOR` over `ops` — or the single operand itself (collapsed; the
    /// caller keeps the operand's negation in that case).
    fn or_of(&mut self, ops: &[(ConceptId, bool)]) -> (ConceptId, bool) {
        if ops.len() == 1 {
            return ops[0];
        }
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCOR);
        for &(o, n) in ops {
            c.add_operand_linker(o, n);
        }
        c.set_operand_count(ops.len() as i64);
        (self.ctx.ontology_arenas_mut().alloc_concept(c), false)
    }
    fn and_of(&mut self, ops: &[(ConceptId, bool)]) -> (ConceptId, bool) {
        if ops.len() == 1 {
            return ops[0];
        }
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCAND);
        for &(o, n) in ops {
            c.add_operand_linker(o, n);
        }
        c.set_operand_count(ops.len() as i64);
        (self.ctx.ontology_arenas_mut().alloc_concept(c), false)
    }
    fn bottom(&mut self) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCBOTTOM);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn some(&mut self, role: RoleId, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCSOME);
        c.set_role(role);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn all(&mut self, role: RoleId, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCALL);
        c.set_role(role);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    fn self_restriction(&mut self, role: RoleId) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCSELF);
        c.set_role(role);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Port of `createTriggerConcept(false)` from Konclude's binary absorber.
    fn implication_trigger(&mut self) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPLTRIG);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Port of `createTriggerPropagationConcept`: when the trigger holds on an
    /// R-successor, `CCIMPLALL(R-, dest)` propagates `dest` to its predecessor.
    fn implication_all(&mut self, inverse_role: RoleId, dest: ConceptId) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPLALL);
        c.set_role(inverse_role);
        c.add_operand_linker(dest, false);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Port of `addUnfoldingConceptForConcept`. Absorption may only extend an
    /// atom/subclass or a generated trigger concept, never a restriction.
    fn add_unfolding(&mut self, host: ConceptId, added: ConceptId, negated: bool) -> bool {
        let op_code = self.ctx.ontology_arenas().concept(host).get_operator_code();
        if !matches!(op_code, op::CCATOM | op::CCSUB | op::CCIMPLTRIG) {
            return false;
        }
        let host_concept = self.ctx.ontology_arenas_mut().concept_mut(host);
        host_concept.add_operand_linker(added, negated);
        host_concept.inc_operand_count(1);
        if op_code == op::CCATOM {
            host_concept.set_operator_code(op::CCSUB);
        }
        true
    }
    /// Port of `buildConceptEquivalentClass`: a still-undefined named atom can
    /// carry one complete equivalent definition directly as `CCEQ`. Positive
    /// use expands conjunctively and negative use disjunctively, so no reverse
    /// TOP GCI is required.
    fn add_equivalent_definition(
        &mut self,
        host: ConceptId,
        definition: ConceptId,
        negated: bool,
    ) -> bool {
        if self.ctx.ontology_arenas().concept(host).get_operator_code() != op::CCATOM {
            return false;
        }
        let concept = self.ctx.ontology_arenas_mut().concept_mut(host);
        concept.set_operator_code(op::CCEQ);
        concept.add_operand_linker(definition, negated);
        concept.set_operand_count(1);
        true
    }
    /// Unqualified `≤n R.⊤` — `CCATMOST` with parameter `n` and NO operand
    /// (empty qualifier ⇒ every R-successor counts). `n = 1` is a functional
    /// role; the completion routes it through `apply_atmost_rule` →
    /// `ht_apply_atmost_merge` (merge excess successors, else clash).
    fn atmost(&mut self, role: RoleId, n: Cint64) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role);
        c.set_parameter(n);
        c.set_operand_count(0);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Qualified `≤n R.C` — `CCATMOST` with parameter `n` and qualifier
    /// operand `C` (the at-most merge counts only `C`-successors).
    fn atmost_q(&mut self, role: RoleId, n: Cint64, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATMOST);
        c.set_role(role);
        c.set_parameter(n);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// Qualified `≥n R.C` — `CCATLEAST` with parameter `n` and qualifier
    /// operand `C` (creates `n` pairwise-distinct `C`-successors).
    fn atleast_q(&mut self, role: RoleId, n: Cint64, filler: (ConceptId, bool)) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCATLEAST);
        c.set_role(role);
        c.set_parameter(n);
        c.add_operand_linker(filler.0, filler.1);
        c.set_operand_count(1);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
    /// `CCIMPL[ head, triggers… ]` — fires `head` once every trigger concept
    /// is present with the OPPOSITE polarity of its linker (see
    /// `apply_implication_rule`): a positive body atom becomes a NEGATED
    /// trigger linker.
    fn implication(
        &mut self,
        head: (ConceptId, bool),
        triggers: &[(ConceptId, bool)],
    ) -> ConceptId {
        let tag = self.fresh_tag();
        let mut c = Concept::new();
        c.set_concept_tag(tag);
        c.set_operator_code(op::CCIMPL);
        c.add_operand_linker(head.0, head.1);
        for &(t, body_neg) in triggers {
            // body atom `C` (body_neg=false) triggers on POSITIVE presence ⇒
            // linker negated=true (the `¬sub` convention); `¬C` the reverse.
            c.add_operand_linker(t, !body_neg);
        }
        c.set_operand_count(1 + triggers.len() as i64);
        self.ctx.ontology_arenas_mut().alloc_concept(c)
    }
}

#[derive(Clone, Copy, Debug)]
struct AbsorptionTrigger {
    concept: ConceptId,
    complexity: Cint64,
}

#[derive(Default)]
struct TriggerCaches {
    full: HashMap<(ConceptId, bool), Option<AbsorptionTrigger>>,
    partial: HashMap<(ConceptId, bool), Option<AbsorptionTrigger>>,
    pairs: HashMap<(ConceptId, ConceptId), AbsorptionTrigger>,
    role_domains: HashMap<RoleId, AbsorptionTrigger>,
}

/// Port of `getUpdatedTriggerComplexities` plus
/// `getImplicationTriggeredConceptForTriggers`: punish over-used trigger hosts,
/// reuse existing trigger pairs, then build Konclude's left-deep binary chain
/// in decreasing (complexity, concept-address) order.
fn combine_absorption_triggers(
    b: &mut Builder,
    mut triggers: Vec<AbsorptionTrigger>,
    caches: &mut TriggerCaches,
) -> Option<AbsorptionTrigger> {
    // CTriggeredImplicationBinaryAbsorberPreProcess.cpp 3336-3346.
    for trigger in &mut triggers {
        let operand_count = b
            .ctx
            .ontology_arenas()
            .concept(trigger.concept)
            .get_operand_count();
        if operand_count > 20 {
            trigger.complexity -= operand_count / 20;
        }
    }

    triggers.sort_by_key(|trigger| trigger.concept.raw);
    triggers.dedup_by_key(|trigger| trigger.concept);

    // Port `findAndReplaceImplicationFromTriggers`: greedily collapse pairs
    // already present in mConceptImplicationImpliedHash before sorting.
    let mut pending = triggers;
    let mut collapsed = Vec::new();
    while !pending.is_empty() {
        let mut trigger = pending.remove(0);
        let mut check_collapsed = false;
        loop {
            let pending_match = pending.iter().position(|other| {
                let key = if trigger.concept.raw <= other.concept.raw {
                    (trigger.concept, other.concept)
                } else {
                    (other.concept, trigger.concept)
                };
                caches.pairs.contains_key(&key)
            });
            if let Some(index) = pending_match {
                let other = pending.remove(index);
                let key = if trigger.concept.raw <= other.concept.raw {
                    (trigger.concept, other.concept)
                } else {
                    (other.concept, trigger.concept)
                };
                trigger = caches.pairs[&key];
                check_collapsed = true;
                continue;
            }
            if check_collapsed {
                let collapsed_match = collapsed.iter().position(|other: &AbsorptionTrigger| {
                    let key = if trigger.concept.raw <= other.concept.raw {
                        (trigger.concept, other.concept)
                    } else {
                        (other.concept, trigger.concept)
                    };
                    caches.pairs.contains_key(&key)
                });
                if let Some(index) = collapsed_match {
                    let other = collapsed.remove(index);
                    let key = if trigger.concept.raw <= other.concept.raw {
                        (trigger.concept, other.concept)
                    } else {
                        (other.concept, trigger.concept)
                    };
                    trigger = caches.pairs[&key];
                    continue;
                }
            }
            break;
        }
        collapsed.push(trigger);
    }

    // CConceptTriggerLinker::operator<= sorts decreasing complexity, then
    // decreasing pointer. Arena ids are the port's stable pointer surrogate.
    collapsed.sort_by(|left, right| {
        right
            .complexity
            .cmp(&left.complexity)
            .then_with(|| right.concept.raw.cmp(&left.concept.raw))
    });
    let mut trigger_it = collapsed.into_iter();
    let mut left = trigger_it.next()?;
    for right in trigger_it {
        let key = if left.concept.raw <= right.concept.raw {
            (left.concept, right.concept)
        } else {
            (right.concept, left.concept)
        };
        let combined = if let Some(&cached) = caches.pairs.get(&key) {
            cached
        } else {
            let implied = b.implication_trigger();
            let implication = b.implication((implied, false), &[(right.concept, false)]);
            if !b.add_unfolding(left.concept, implication, false) {
                return None;
            }
            let combined = AbsorptionTrigger {
                concept: implied,
                complexity: left.complexity + right.complexity,
            };
            caches.pairs.insert(key, combined);
            combined
        };
        left = combined;
    }
    Some(left)
}

fn role_domain_trigger(
    b: &mut Builder,
    role: RoleId,
    inverse_role: RoleId,
    caches: &mut TriggerCaches,
) -> AbsorptionTrigger {
    if let Some(&trigger) = caches.role_domains.get(&role) {
        return trigger;
    }
    let concept = b.implication_trigger();
    let link = super::model::substrate::NegLink {
        target: concept,
        negated: false,
    };
    b.ctx
        .ontology_arenas_mut()
        .role_mut(role)
        .domain_linker
        .push(link);
    b.ctx
        .ontology_arenas_mut()
        .role_mut(inverse_role)
        .range_linker
        .push(link);
    let trigger = AbsorptionTrigger {
        concept,
        complexity: 1,
    };
    caches.role_domains.insert(role, trigger);
    trigger
}

/// Role-domain marker fragment of Konclude's `CBranchTriggerPreProcess`.
/// For every disjunctive concept, qualified universal/cardinality leaves are
/// indexed by an empty `CCIMPLTRIG` on the restriction role's domain. The
/// completion-side branching metadata is separate; this terminology marker
/// is also required by saturation and common-concept extraction.
fn install_branch_role_domain_triggers(b: &mut Builder, caches: &mut TriggerCaches) -> usize {
    let concept_count = b.ctx.ontology_arenas().concept_count();
    let mut roles = BTreeSet::new();
    for index in 0..concept_count {
        let concept = ConceptId::new(index as Cint64);
        let (op_code, operand_count) = {
            let concept = b.ctx.ontology_arenas().concept(concept);
            (concept.get_operator_code(), concept.get_operand_count())
        };
        if operand_count <= 1 || !matches!(op_code, op::CCAND | op::CCEQ | op::CCOR) {
            continue;
        }
        let mut pending = vec![(concept, op_code != op::CCOR)];
        while let Some((candidate, negated)) = pending.pop() {
            let (candidate_code, candidate_role, candidate_operands) = {
                let candidate = b.ctx.ontology_arenas().concept(candidate);
                (
                    candidate.get_operator_code(),
                    candidate.get_role(),
                    candidate.get_operand_list().to_vec(),
                )
            };
            if (!negated && candidate_code == op::CCOR)
                || (negated && matches!(candidate_code, op::CCAND | op::CCEQ))
            {
                pending.extend(
                    candidate_operands
                        .into_iter()
                        .map(|operand| (operand.target, operand.negated ^ negated)),
                );
                continue;
            }
            let role_trigger = (!negated && matches!(candidate_code, op::CCALL | op::CCATMOST))
                || (negated
                    && matches!(candidate_code, op::CCSOME | op::CCATLEAST)
                    && !candidate_operands.is_empty());
            if role_trigger && candidate_role.is_some() {
                roles.insert(candidate_role.raw);
            }
        }
    }

    let mut installed = 0;
    for role in roles.into_iter().map(RoleId::new) {
        let inverse = b.ctx.ontology_arenas().role(role).get_inverse_role();
        if inverse.is_none() {
            continue;
        }
        let existed = caches.role_domains.contains_key(&role);
        role_domain_trigger(b, role, inverse, caches);
        installed += usize::from(!existed);
    }
    installed
}

/// Faithful fragment of Konclude's `getTriggersForConcept`: atoms are direct
/// triggers, Boolean structure is recursively compiled, and existential
/// structure becomes an inverse-role `CCIMPLALL` trigger-propagation chain.
fn full_absorption_trigger(
    b: &mut Builder,
    literal: (ConceptId, bool),
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> Option<AbsorptionTrigger> {
    if let Some(cached) = caches.full.get(&literal) {
        return *cached;
    }
    let (concept, negated) = literal;
    let (op_code, parameter, role, operands) = {
        let c = b.ctx.ontology_arenas().concept(concept);
        (
            c.get_operator_code(),
            c.get_parameter(),
            c.get_role(),
            c.get_operand_list().to_vec(),
        )
    };
    let result =
        if !negated && matches!(op_code, op::CCATOM | op::CCSUB | op::CCTOP | op::CCIMPLTRIG) {
            Some(AbsorptionTrigger {
                concept,
                complexity: 1,
            })
        } else if (!negated && matches!(op_code, op::CCAND | op::CCEQ))
            || (negated && op_code == op::CCOR)
        {
            let mut triggers = Vec::new();
            for operand in operands {
                triggers.push(full_absorption_trigger(
                    b,
                    (operand.target, operand.negated ^ negated),
                    role_inverses,
                    caches,
                )?);
            }
            combine_absorption_triggers(b, triggers, caches)
        } else if (!negated && op_code == op::CCOR)
            || (negated && matches!(op_code, op::CCAND | op::CCEQ))
        {
            let mut alternatives = Vec::new();
            for operand in operands {
                let trigger = full_absorption_trigger(
                    b,
                    (operand.target, operand.negated ^ negated),
                    role_inverses,
                    caches,
                )?;
                alternatives.push(trigger);
            }
            if alternatives.len() <= 1 {
                alternatives.into_iter().next()
            } else {
                let implied = b.implication_trigger();
                let complexity_sum: Cint64 =
                    alternatives.iter().map(|trigger| trigger.complexity).sum();
                let trigger_count = alternatives.len() as Cint64;
                for trigger in alternatives {
                    if !b.add_unfolding(trigger.concept, implied, false) {
                        return None;
                    }
                }
                // Exact C++ `(triggerComplexity + 1) / triggerCount`.
                Some(AbsorptionTrigger {
                    concept: implied,
                    complexity: (complexity_sum + 1) / trigger_count,
                })
            }
        } else if (!negated && op_code == op::CCSOME)
            || (negated && op_code == op::CCALL)
            || (!negated && op_code == op::CCATLEAST && parameter == 1)
            || (negated && op_code == op::CCATMOST && parameter == 0)
        {
            let &inverse = role_inverses.get(&role)?;
            if operands.is_empty() {
                Some(role_domain_trigger(b, role, inverse, caches))
            } else if operands.len() == 1
                && !operands[0].negated
                && b.ctx
                    .ontology_arenas()
                    .concept(operands[0].target)
                    .get_operator_code()
                    == op::CCTOP
                && !negated
            {
                // `∃R.Thing` (and `≥1 R.Thing`) is exactly the existence of an
                // R edge. Konclude uses the role-domain trigger directly; TOP
                // is not an unfolding host for a successor propagation.
                Some(role_domain_trigger(b, role, inverse, caches))
            } else {
                let mut filler_triggers = Vec::new();
                for operand in operands {
                    let operand_negated = if matches!(op_code, op::CCATLEAST | op::CCATMOST) {
                        operand.negated
                    } else {
                        operand.negated ^ negated
                    };
                    filler_triggers.push(full_absorption_trigger(
                        b,
                        (operand.target, operand_negated),
                        role_inverses,
                        caches,
                    )?);
                }
                let filler = combine_absorption_triggers(b, filler_triggers, caches)?;
                let propagated = b.implication_trigger();
                let propagation = b.implication_all(inverse, propagated);
                if !b.add_unfolding(filler.concept, propagation, false) {
                    None
                } else {
                    Some(AbsorptionTrigger {
                        concept: propagated,
                        complexity: filler.complexity + 1,
                    })
                }
            }
        } else {
            None
        };
    caches.full.insert(literal, result);
    result
}

/// Collect the top-level conjunctive triggers for one absorbed GCI literal.
/// Konclude passes all of these to the same final implication and chooses the
/// most complex one as its unfolding host. It does not first collapse them to
/// a generated binary-trigger tree.
fn collect_full_absorption_triggers(
    b: &mut Builder,
    literal: (ConceptId, bool),
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
    triggers: &mut Vec<AbsorptionTrigger>,
) -> bool {
    let (concept, negated) = literal;
    let (op_code, operands) = {
        let concept = b.ctx.ontology_arenas().concept(concept);
        (
            concept.get_operator_code(),
            concept.get_operand_list().to_vec(),
        )
    };
    if (!negated && matches!(op_code, op::CCAND | op::CCEQ)) || (negated && op_code == op::CCOR) {
        return operands.into_iter().all(|operand| {
            collect_full_absorption_triggers(
                b,
                (operand.target, operand.negated ^ negated),
                role_inverses,
                caches,
                triggers,
            )
        });
    }
    if let Some(trigger) = full_absorption_trigger(b, literal, role_inverses, caches) {
        triggers.push(trigger);
        true
    } else {
        false
    }
}

/// Port of the null-`firstImplicationConcept` path used by
/// `createGCIAbsorbedTriggeredImplication`: combine every condition into the
/// reusable binary trigger chain, then unfold the conclusion from its final
/// trigger concept.
fn attach_implied_to_combined_trigger(
    b: &mut Builder,
    implied: (ConceptId, bool),
    triggers: Vec<AbsorptionTrigger>,
    caches: &mut TriggerCaches,
) -> bool {
    let Some(trigger) = combine_absorption_triggers(b, triggers, caches) else {
        return false;
    };
    b.add_unfolding(trigger.concept, implied.0, implied.1)
}

/// Port of `getPartialTriggersForConcept`. The returned trigger is a necessary
/// condition only; callers unfold the original residual GCI from it, exactly as
/// `createGCIPartialAbsorbedTriggeredImplication` does in Konclude.
fn partial_absorption_trigger(
    b: &mut Builder,
    literal: (ConceptId, bool),
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> Option<AbsorptionTrigger> {
    if let Some(trigger) = full_absorption_trigger(b, literal, role_inverses, caches) {
        return Some(trigger);
    }
    if let Some(cached) = caches.partial.get(&literal) {
        return *cached;
    }
    let (concept, negated) = literal;
    let (op_code, role, operands) = {
        let c = b.ctx.ontology_arenas().concept(concept);
        (
            c.get_operator_code(),
            c.get_role(),
            c.get_operand_list().to_vec(),
        )
    };
    let result = if (!negated && op_code == op::CCAND) || (negated && op_code == op::CCOR) {
        let triggers: Vec<_> = operands
            .into_iter()
            .filter_map(|operand| {
                partial_absorption_trigger(
                    b,
                    (operand.target, operand.negated ^ negated),
                    role_inverses,
                    caches,
                )
            })
            .collect();
        combine_absorption_triggers(b, triggers, caches)
    } else if (!negated && op_code == op::CCOR)
        || (negated && matches!(op_code, op::CCAND | op::CCEQ))
    {
        let mut alternatives = Vec::new();
        for operand in operands {
            alternatives.push(partial_absorption_trigger(
                b,
                (operand.target, operand.negated ^ negated),
                role_inverses,
                caches,
            )?);
        }
        if alternatives.len() <= 1 {
            alternatives.into_iter().next()
        } else {
            let implied = b.implication_trigger();
            // Exact partial-trigger code initializes the minimum at zero.
            let complexity = alternatives
                .iter()
                .fold(0, |minimum, trigger| minimum.min(trigger.complexity));
            for trigger in alternatives {
                if !b.add_unfolding(trigger.concept, implied, false) {
                    return None;
                }
            }
            Some(AbsorptionTrigger {
                concept: implied,
                complexity,
            })
        }
    } else if (!negated && matches!(op_code, op::CCSOME | op::CCSELF | op::CCATLEAST))
        || (negated && matches!(op_code, op::CCALL | op::CCATMOST))
    {
        let &inverse = role_inverses.get(&role)?;
        let mut filler_triggers = Vec::new();
        for operand in operands {
            if let Some(trigger) = partial_absorption_trigger(
                b,
                (
                    operand.target,
                    operand.negated ^ (negated && op_code == op::CCALL),
                ),
                role_inverses,
                caches,
            ) {
                filler_triggers.push(trigger);
            }
        }
        if filler_triggers.is_empty() {
            Some(role_domain_trigger(b, role, inverse, caches))
        } else {
            let filler = combine_absorption_triggers(b, filler_triggers, caches)?;
            let propagated = b.implication_trigger();
            let propagation = b.implication_all(inverse, propagated);
            if !b.add_unfolding(filler.concept, propagation, false) {
                None
            } else {
                Some(AbsorptionTrigger {
                    concept: propagated,
                    complexity: filler.complexity + 1,
                })
            }
        }
    } else {
        None
    };
    caches.partial.insert(literal, result);
    result
}

/// Port of the full/partial GCI split in
/// `createGCIAbsorbedTriggeredImplication`. `body` contains conjunctive
/// antecedents; `heads` contains the disjunctive consequent. Fully triggerable
/// head complements move into the antecedent. If full absorption is impossible,
/// a necessary partial trigger unfolds the original GCI instead.
fn absorb_concept_disjunction(
    b: &mut Builder,
    body: &[(ConceptId, bool)],
    heads: &[(ConceptId, bool)],
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> bool {
    let mut full_triggers = Vec::new();
    let mut body_fully_triggerable = true;
    for &literal in body {
        if !collect_full_absorption_triggers(b, literal, role_inverses, caches, &mut full_triggers)
        {
            body_fully_triggerable = false;
        }
    }

    let mut residual_heads = Vec::new();
    for &(concept, negated) in heads {
        if !collect_full_absorption_triggers(
            b,
            (concept, !negated),
            role_inverses,
            caches,
            &mut full_triggers,
        ) {
            residual_heads.push((concept, negated));
        }
    }

    if body_fully_triggerable && !full_triggers.is_empty() {
        let implied = if residual_heads.is_empty() {
            (b.bottom(), false)
        } else {
            b.or_of(&residual_heads)
        };
        return attach_implied_to_combined_trigger(b, implied, full_triggers, caches);
    }

    // Partial absorption is only a gate. Preserve the complete original GCI
    // under that gate, as Konclude does before installing branch metadata.
    let mut partial_triggers = Vec::new();
    for &literal in body {
        if let Some(trigger) = partial_absorption_trigger(b, literal, role_inverses, caches) {
            partial_triggers.push(trigger);
        }
    }
    for &(concept, negated) in heads {
        if let Some(trigger) =
            partial_absorption_trigger(b, (concept, !negated), role_inverses, caches)
        {
            partial_triggers.push(trigger);
        }
    }
    let Some(trigger) = combine_absorption_triggers(b, partial_triggers, caches) else {
        return false;
    };
    let mut original_disjunction: Vec<(ConceptId, bool)> = body
        .iter()
        .map(|&(concept, negated)| (concept, !negated))
        .collect();
    original_disjunction.extend_from_slice(heads);
    let original = if original_disjunction.is_empty() {
        (b.bottom(), false)
    } else {
        b.or_of(&original_disjunction)
    };
    b.add_unfolding(trigger.concept, original.0, original.1)
}

/// Build the normalized frontend concept directly in Konclude's native DAG.
/// This mirrors `CConcreteOntologyUpdateBuilder::buildClassConcept`: structural
/// expressions are shared, named classes retain their fixed terminology atom,
/// and inverse role expressions use the role's wired inverse object.
fn build_source_concept(
    b: &mut Builder,
    source: &SourceConcept,
    concept_index: &HashMap<&str, usize>,
    role_index: &HashMap<&str, usize>,
    named: &[ConceptId],
    roles: &[RoleId],
    inv_roles: &[RoleId],
    cache: &mut HashMap<SourceConcept, (ConceptId, bool)>,
) -> Option<(ConceptId, bool)> {
    if let Some(&built) = cache.get(source) {
        return Some(built);
    }
    let role = |r: &SourceRole| -> Option<RoleId> {
        match r {
            SourceRole::Name(name) => role_index.get(name.as_str()).map(|&i| roles[i]),
            SourceRole::Inverse(name) => role_index.get(name.as_str()).map(|&i| inv_roles[i]),
            SourceRole::Universal => None,
        }
    };
    let built = match source {
        SourceConcept::Name(name) => {
            let i = *concept_index.get(name.as_str())?;
            (named[i], false)
        }
        SourceConcept::Top => (b.ctx.processing_data_box().ontology_top_concept(), false),
        SourceConcept::Bottom => (b.bottom(), false),
        SourceConcept::Nominal(_) => return None,
        SourceConcept::Not(operand) => {
            let (concept, negated) = build_source_concept(
                b,
                operand,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                cache,
            )?;
            (concept, !negated)
        }
        SourceConcept::And(operands) | SourceConcept::Or(operands) => {
            let built_operands: Option<Vec<_>> = operands
                .iter()
                .map(|operand| {
                    build_source_concept(
                        b,
                        operand,
                        concept_index,
                        role_index,
                        named,
                        roles,
                        inv_roles,
                        cache,
                    )
                })
                .collect();
            let built_operands = built_operands?;
            if matches!(source, SourceConcept::And(_)) {
                b.and_of(&built_operands)
            } else {
                b.or_of(&built_operands)
            }
        }
        SourceConcept::Exists(r, filler) | SourceConcept::Forall(r, filler) => {
            let filler = build_source_concept(
                b,
                filler,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                cache,
            )?;
            let role = role(r)?;
            if matches!(source, SourceConcept::Exists(..)) {
                (b.some(role, filler), false)
            } else {
                (b.all(role, filler), false)
            }
        }
        SourceConcept::AtLeast(n, r, filler) | SourceConcept::AtMost(n, r, filler) => {
            let filler = build_source_concept(
                b,
                filler,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                cache,
            )?;
            let role = role(r)?;
            if matches!(source, SourceConcept::AtLeast(..)) {
                (b.atleast_q(role, *n, filler), false)
            } else {
                (b.atmost_q(role, *n, filler), false)
            }
        }
        SourceConcept::HasSelf(r) => (b.self_restriction(role(r)?), false),
    };
    cache.insert(source.clone(), built);
    Some(built)
}

fn source_role_id(
    role: &SourceRole,
    role_index: &HashMap<&str, usize>,
    roles: &[RoleId],
    inv_roles: &[RoleId],
) -> Option<RoleId> {
    match role {
        SourceRole::Name(name) => role_index.get(name.as_str()).map(|&i| roles[i]),
        SourceRole::Inverse(name) => role_index.get(name.as_str()).map(|&i| inv_roles[i]),
        SourceRole::Universal => None,
    }
}

#[derive(Clone, Copy)]
enum SourceEncoding {
    Direct,
    RoleLink,
    AbsorbedGci,
    TopGci,
    Unsupported,
}

/// Port of `CConcreteOntologyUpdateBuilder::buildConceptSubClassInclusion`.
/// Atomic left sides become native `CCSUB` unfoldings; only a structural left
/// side reaches the binary GCI absorber. Domain/range-shaped inclusions are
/// stored on the role, matching Konclude's object-property axiom builder.
#[allow(clippy::too_many_arguments)]
fn encode_source_subclass(
    b: &mut Builder,
    left: &SourceConcept,
    right: &SourceConcept,
    concept_index: &HashMap<&str, usize>,
    role_index: &HashMap<&str, usize>,
    named: &[ConceptId],
    roles: &[RoleId],
    inv_roles: &[RoleId],
    role_inverses: &HashMap<RoleId, RoleId>,
    concept_cache: &mut HashMap<SourceConcept, (ConceptId, bool)>,
    trigger_caches: &mut TriggerCaches,
    tbox: &mut Vec<ConceptId>,
    top_gcis: &mut Vec<ConceptId>,
) -> SourceEncoding {
    // The frontend represents complex ObjectPropertyDomain/Range axioms by
    // their DL-equivalent subclass forms. Konclude keeps these as role links.
    if let SourceConcept::Exists(role, filler) = left {
        if matches!(filler.as_ref(), SourceConcept::Top) {
            let Some(role) = source_role_id(role, role_index, roles, inv_roles) else {
                return SourceEncoding::Unsupported;
            };
            let Some((target, negated)) = build_source_concept(
                b,
                right,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                concept_cache,
            ) else {
                return SourceEncoding::Unsupported;
            };
            let link = super::model::substrate::NegLink { target, negated };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .domain_linker
                .push(link);
            if let Some(&inverse) = role_inverses.get(&role) {
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inverse)
                    .range_linker
                    .push(link);
            }
            return SourceEncoding::RoleLink;
        }
    }
    if matches!(left, SourceConcept::Top) {
        if let SourceConcept::Forall(role, filler) = right {
            let Some(role) = source_role_id(role, role_index, roles, inv_roles) else {
                return SourceEncoding::Unsupported;
            };
            let Some((target, negated)) = build_source_concept(
                b,
                filler,
                concept_index,
                role_index,
                named,
                roles,
                inv_roles,
                concept_cache,
            ) else {
                return SourceEncoding::Unsupported;
            };
            let link = super::model::substrate::NegLink { target, negated };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .range_linker
                .push(link);
            if let Some(&inverse) = role_inverses.get(&role) {
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inverse)
                    .domain_linker
                    .push(link);
            }
            return SourceEncoding::RoleLink;
        }
    }

    let Some(left_built) = build_source_concept(
        b,
        left,
        concept_index,
        role_index,
        named,
        roles,
        inv_roles,
        concept_cache,
    ) else {
        return SourceEncoding::Unsupported;
    };
    let Some(right_built) = build_source_concept(
        b,
        right,
        concept_index,
        role_index,
        named,
        roles,
        inv_roles,
        concept_cache,
    ) else {
        return SourceEncoding::Unsupported;
    };

    if matches!(left, SourceConcept::Name(_))
        && !left_built.1
        && b.add_unfolding(left_built.0, right_built.0, right_built.1)
    {
        return SourceEncoding::Direct;
    }

    if absorb_concept_disjunction(
        b,
        &[left_built],
        &[right_built],
        role_inverses,
        trigger_caches,
    ) {
        return SourceEncoding::AbsorbedGci;
    }

    // Exact fallback: TOP carries `¬left ∨ right`, so every node checks the
    // original GCI even when no binary trigger can be constructed.
    let disjunction = b.or_of(&[(left_built.0, !left_built.1), right_built]);
    tbox.push(disjunction.0);
    top_gcis.push(disjunction.0);
    SourceEncoding::TopGci
}

fn role_tree_trigger(
    b: &mut Builder,
    node: usize,
    children: &HashMap<usize, Vec<(usize, usize)>>,
    local: &HashMap<usize, Vec<(ConceptId, bool)>>,
    roles: &[RoleId],
    inv_roles: &[RoleId],
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
    visiting: &mut BTreeSet<usize>,
) -> Option<AbsorptionTrigger> {
    if !visiting.insert(node) {
        return None;
    }
    let mut triggers = Vec::new();
    for &literal in local.get(&node).into_iter().flatten() {
        triggers.push(full_absorption_trigger(b, literal, role_inverses, caches)?);
    }
    for &(role_index, child) in children.get(&node).into_iter().flatten() {
        if let Some(child_trigger) = role_tree_trigger(
            b,
            child,
            children,
            local,
            roles,
            inv_roles,
            role_inverses,
            caches,
            visiting,
        ) {
            let propagated = b.implication_trigger();
            let propagation = b.implication_all(inv_roles[role_index], propagated);
            if !b.add_unfolding(child_trigger.concept, propagation, false) {
                return None;
            }
            triggers.push(AbsorptionTrigger {
                concept: propagated,
                complexity: child_trigger.complexity + 1,
            });
        } else if local.get(&child).map_or(true, Vec::is_empty)
            && children.get(&child).map_or(true, Vec::is_empty)
        {
            triggers.push(role_domain_trigger(
                b,
                roles[role_index],
                inv_roles[role_index],
                caches,
            ));
        } else {
            return None;
        }
    }
    visiting.remove(&node);
    combine_absorption_triggers(b, triggers, caches)
}

/// Clause-graph counterpart of Konclude's recursive existential trigger
/// construction. A rooted role tree is compiled into nested inverse-role
/// `CCIMPLALL` propagation, rather than emitted as an unsupported multi-role
/// DL clause.
fn absorb_role_tree_clause(
    b: &mut Builder,
    cl: &HtClause,
    resolved: &[(ConceptId, bool)],
    roles: &[RoleId],
    inv_roles: &[RoleId],
    role_inverses: &HashMap<RoleId, RoleId>,
    caches: &mut TriggerCaches,
) -> bool {
    let mut children: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    let mut incoming: HashMap<usize, usize> = HashMap::new();
    let mut local: HashMap<usize, Vec<(ConceptId, bool)>> = HashMap::new();
    for atom in &cl.body {
        match atom {
            HAtom::Role { r, s, t } if s != t => {
                if incoming.insert(*t, *s).is_some() {
                    return false;
                }
                children.entry(*s).or_default().push((*r, *t));
            }
            HAtom::Concept { neg, c, t } => {
                local
                    .entry(*t)
                    .or_default()
                    .push((resolved[*c].0, resolved[*c].1 ^ *neg));
            }
            _ => return false,
        }
    }
    if incoming.contains_key(&0) {
        return false;
    }
    let mut all_nodes: BTreeSet<usize> = BTreeSet::from([0]);
    all_nodes.extend(incoming.keys().copied());
    all_nodes.extend(children.keys().copied());
    if all_nodes
        .iter()
        .any(|&node| node != 0 && !incoming.contains_key(&node))
    {
        return false;
    }
    let Some(trigger) = role_tree_trigger(
        b,
        0,
        &children,
        &local,
        roles,
        inv_roles,
        role_inverses,
        caches,
        &mut BTreeSet::new(),
    ) else {
        return false;
    };
    let mut heads = Vec::new();
    for atom in &cl.head {
        match atom {
            HAtom::Concept { neg, c, t } if *t == 0 => {
                heads.push((resolved[*c].0, resolved[*c].1 ^ *neg));
            }
            HAtom::Exist { r, neg, c, t } if *t == 0 => {
                heads.push((
                    b.some(roles[*r], (resolved[*c].0, resolved[*c].1 ^ *neg)),
                    false,
                ));
            }
            _ => return false,
        }
    }
    let implied = if heads.is_empty() {
        (b.bottom(), false)
    } else {
        b.or_of(&heads)
    };
    b.add_unfolding(trigger.concept, implied.0, implied.1)
}

/// Dense equivalent of Konclude's `QSet<TConNegPair>` for one ontology.
/// Concept ids are arena-dense, so generation stamps implement the same
/// signed-concept set without hashing every pointer pair. `entries` keeps the
/// iterable members; root clearing is O(1), and branch rollback clears only
/// entries inserted since its saved mark.
struct DenseSignedConceptSet {
    marks: Vec<u32>,
    generation: u32,
    entries: Vec<(ConceptId, bool)>,
}

impl DenseSignedConceptSet {
    fn new(concept_count: usize) -> Self {
        Self {
            marks: vec![0; concept_count.saturating_mul(2)],
            generation: 1,
            entries: Vec::new(),
        }
    }

    #[inline]
    fn key(entry: (ConceptId, bool)) -> usize {
        entry.0.index() * 2 + usize::from(entry.1)
    }

    #[inline]
    fn insert(&mut self, entry: (ConceptId, bool)) -> bool {
        let key = Self::key(entry);
        if self.marks[key] == self.generation {
            return false;
        }
        self.marks[key] = self.generation;
        self.entries.push(entry);
        true
    }

    #[inline]
    fn contains(&self, entry: (ConceptId, bool)) -> bool {
        self.marks[Self::key(entry)] == self.generation
    }

    fn clear(&mut self) {
        self.entries.clear();
        self.generation = self.generation.wrapping_add(1);
        if self.generation == 0 {
            self.marks.fill(0);
            self.generation = 1;
        }
    }

    fn rollback(&mut self, mark: usize) {
        while self.entries.len() > mark {
            let entry = self.entries.pop().expect("branch mark within set");
            self.marks[Self::key(entry)] = 0;
        }
    }

    fn extend(&mut self, entries: &[(ConceptId, bool)]) {
        for &entry in entries {
            self.insert(entry);
        }
    }

    fn retain_members_of(&mut self, other: &Self) {
        let mut write = 0usize;
        for read in 0..self.entries.len() {
            let entry = self.entries[read];
            if other.contains(entry) {
                self.entries[write] = entry;
                write += 1;
            } else {
                self.marks[Self::key(entry)] = 0;
            }
        }
        self.entries.truncate(write);
    }
}

/// Two branch sets per nested disjunction. Konclude's local QSets reuse their
/// allocations through Qt's containers; this pool gives the Rust port the
/// same lifetime shape without allocating arena-sized marker vectors for each
/// of the 73k disjunction visits in ore_ont_3215.
#[derive(Default)]
struct CommonDisjunctScratch {
    levels: Vec<Option<(DenseSignedConceptSet, DenseSignedConceptSet)>>,
}

impl CommonDisjunctScratch {
    fn take(
        &mut self,
        depth: usize,
        concept_count: usize,
    ) -> (DenseSignedConceptSet, DenseSignedConceptSet) {
        while self.levels.len() <= depth {
            self.levels.push(None);
        }
        self.levels[depth].take().unwrap_or_else(|| {
            (
                DenseSignedConceptSet::new(concept_count),
                DenseSignedConceptSet::new(concept_count),
            )
        })
    }

    fn put(&mut self, depth: usize, sets: (DenseSignedConceptSet, DenseSignedConceptSet)) {
        debug_assert!(self.levels[depth].is_none());
        self.levels[depth] = Some(sets);
    }
}

fn collect_common_disjunct_concepts(
    arenas: &super::model::ontology::OntologyArenas,
    concept: ConceptId,
    negated: bool,
    collect: &mut DenseSignedConceptSet,
    considered: &mut DenseSignedConceptSet,
    cache: &mut HashMap<(ConceptId, bool), Vec<(ConceptId, bool)>>,
    scratch: &mut CommonDisjunctScratch,
    disjunction_depth: usize,
) {
    let entry = (concept, negated);
    if !considered.insert(entry) {
        return;
    }
    collect.insert(entry);
    let (op_code, operand_count) = {
        let c = arenas.concept(concept);
        (c.get_operator_code(), c.get_operand_count() as usize)
    };

    let unfolds = (!negated
        && (matches!(op_code, op::CCSUB | op::CCEQ | op::CCAND)
            || (op_code == op::CCOR && operand_count == 1)))
        || (negated
            && (op_code == op::CCOR
                || (operand_count == 1 && matches!(op_code, op::CCAND | op::CCEQ))));
    if unfolds {
        for operand_index in 0..operand_count {
            // Konclude advances one intrusive operand linker at a time. Copy
            // one small arena link, rather than cloning the whole operand Vec
            // on every recursive visit.
            let operand = arenas.concept(concept).get_operand_list()[operand_index];
            collect_common_disjunct_concepts(
                arenas,
                operand.target,
                operand.negated ^ negated,
                collect,
                considered,
                cache,
                scratch,
                disjunction_depth,
            );
        }
        return;
    }

    let is_disjunction =
        (!negated && op_code == op::CCOR) || (negated && matches!(op_code, op::CCAND | op::CCEQ));
    if !is_disjunction {
        return;
    }

    let key = (concept, negated);
    if let Some(cached) = cache.get(&key) {
        // Konclude stores a pointer to the cached QSet and inserts its members
        // directly into the caller's set (cpp 147-185). Cloning the whole set
        // here retained gigabytes on disjunction-heavy terminologies such as
        // ore_ont_3215 and defeated the cache's purpose.
        collect.extend(cached);
        return;
    }

    let concept_count = arenas.concept_count() as usize;
    let (mut intersection, mut next) = scratch.take(disjunction_depth, concept_count);
    intersection.clear();
    next.clear();
    if operand_count > 0 {
        // QSet copies in Konclude are implicitly shared. Reproduce their
        // branch-local semantics without deep-cloning the complete visited
        // set: record additions, then roll them back after each disjunct.
        let first = arenas.concept(concept).get_operand_list()[0];
        let mark = considered.entries.len();
        collect_common_disjunct_concepts(
            arenas,
            first.target,
            first.negated ^ negated,
            &mut intersection,
            considered,
            cache,
            scratch,
            disjunction_depth + 1,
        );
        considered.rollback(mark);
        for operand_index in 1..operand_count {
            if intersection.entries.is_empty() {
                break;
            }
            next.clear();
            let operand = arenas.concept(concept).get_operand_list()[operand_index];
            let mark = considered.entries.len();
            collect_common_disjunct_concepts(
                arenas,
                operand.target,
                operand.negated ^ negated,
                &mut next,
                considered,
                cache,
                scratch,
                disjunction_depth + 1,
            );
            considered.rollback(mark);
            intersection.retain_members_of(&next);
        }
    }
    collect.extend(&intersection.entries);
    // Konclude owns a separate cached QSet pointer. Cache its iterable
    // members; membership tests stay in the dense scratch sets above.
    cache.insert(key, intersection.entries.clone());
    scratch.put(disjunction_depth, (intersection, next));
}

/// Port of Konclude `CCommonDisjunctConceptExtractionPreProcess` over the
/// completed bridge terminology.  It materialises the producer data consumed
/// by `initializeORProcessing`, rather than recomputing common concepts in the
/// completion hot loop.
fn extract_common_disjunct_replacements(ctx: &mut CalculationAlgorithmContextBase) -> usize {
    let concept_count = ctx.ontology_arenas().concept_count() as usize;
    let mut cache = HashMap::new();
    let mut considered = DenseSignedConceptSet::new(concept_count);
    let mut common = DenseSignedConceptSet::new(concept_count);
    let mut scratch = CommonDisjunctScratch::default();
    let mut extracted = Vec::new();
    for index in 0..concept_count {
        let concept = ConceptId::new(index as Cint64);
        let (op_code, operand_count) = {
            let c = ctx.ontology_arenas().concept(concept);
            (c.get_operator_code(), c.get_operand_count())
        };
        if operand_count < 1 || !matches!(op_code, op::CCAND | op::CCEQ | op::CCOR) {
            continue;
        }
        let negated = matches!(op_code, op::CCAND | op::CCEQ);
        considered.clear();
        common.clear();
        collect_common_disjunct_concepts(
            ctx.ontology_arenas(),
            concept,
            negated,
            &mut common,
            &mut considered,
            &mut cache,
            &mut scratch,
            0,
        );
        if common.entries.len() > 1 {
            let mut common: Vec<_> = common
                .entries
                .iter()
                .copied()
                .filter(|&entry| entry != (concept, negated))
                .collect();
            if common.is_empty() {
                continue;
            }
            common.sort_by_key(|(concept, negated)| {
                (
                    ctx.ontology_arenas().concept(*concept).get_concept_tag(),
                    *negated,
                )
            });
            extracted.push((concept, common));
        }
    }

    for (concept, common) in &extracted {
        let concept_data = ctx.ontology_arenas().concept(*concept).get_concept_data();
        let process_data = if concept_data == INVALID {
            let id = ctx
                .ontology_arenas_mut()
                .alloc_concept_process_data(ConceptProcessData::new());
            ctx.ontology_arenas_mut()
                .concept_mut(*concept)
                .set_concept_data(id.raw);
            id
        } else {
            Id::new(concept_data)
        };
        let previous = ctx
            .ontology_arenas()
            .concept_process_data(process_data)
            .get_replacement_data();
        let replacement = if previous.is_some() {
            previous
        } else {
            let id = ctx
                .ontology_arenas_mut()
                .alloc_replacement_data(ReplacementData::new());
            ctx.ontology_arenas_mut()
                .concept_process_data_mut(process_data)
                .set_replacement_data(id);
            id
        };
        ctx.ontology_arenas_mut()
            .replacement_data_mut(replacement)
            .common_disjunct_concepts = common
            .iter()
            .map(|(concept, negated)| NegLink {
                target: *concept,
                negated: *negated,
            })
            .collect();
    }
    extracted.len()
}

/// Build the bridged terminology for `tin` into `ctx`'s ontology arenas.
///
/// The context must be freshly constructed (the bridge owns tag allocation
/// from [`TAG_BASE`]; the TOP sentinel at tag 1 is seeded by the caller
/// exactly as `classify_test::new_env` does).
pub fn bridge_tinput(ctx: &mut CalculationAlgorithmContextBase, tin: &TInput) -> Bridged {
    bridge_tinput_with_trigger_absorption(ctx, tin, std::env::var_os("KM_TRIGGER_ABSORB").is_some())
}

/// Environment-independent terminology builder used by focused absorber
/// tests. Production continues to select the same option in [`bridge_tinput`].
fn bridge_tinput_with_trigger_absorption(
    ctx: &mut CalculationAlgorithmContextBase,
    tin: &TInput,
    trigger_absorb: bool,
) -> Bridged {
    let source_mode = trigger_absorb
        && !tin.source_axioms.is_empty()
        && std::env::var_os("KM_NO_SOURCE_TBOX").is_none();
    // Konclude distinguishes every concept in the terminology vector from
    // the active OWL classes it classifies. Frontend Q_/definer concepts are
    // anonymous structural concepts in Konclude; assigning class-name linkers
    // to all TInput atoms made both saturation and KPSet treat 113,187 such
    // markers as classes on ore_ont_3215. `queries` is the frontend's active
    // named-class set; an empty list retains the legacy all-active test input.
    let mut active_class = vec![tin.queries.is_empty(); tin.concepts.len()];
    for &query in &tin.queries {
        if let Some(active) = active_class.get_mut(query) {
            *active = true;
        }
    }
    let bridge_phase_trace = std::env::var_os("KM_BRIDGE_PHASES").is_some();
    let bridge_started = std::time::Instant::now();
    let mut bridge_phase_started = bridge_started;
    macro_rules! bridge_phase {
        ($name:expr) => {
            if bridge_phase_trace {
                let now = std::time::Instant::now();
                eprintln!(
                    "BRIDGE-PHASE {} delta={:.3}s total={:.3}s",
                    $name,
                    now.duration_since(bridge_phase_started).as_secs_f64(),
                    now.duration_since(bridge_started).as_secs_f64(),
                );
                bridge_phase_started = now;
            }
        };
    }
    let mut b = Builder {
        ctx,
        next_tag: TAG_BASE + tin.concepts.len() as Cint64,
    };
    let named: Vec<ConceptId> = (0..tin.concepts.len())
        .map(|i| {
            let tag = TAG_BASE + i as Cint64;
            let concept = b.atom(tag);
            if active_class[i] {
                b.ctx
                    .ontology_arenas_mut()
                    .concept_mut(concept)
                    .add_class_name_linker(NameId::new(tag));
            }
            concept
        })
        .collect();
    bridge_phase!("named-and-roles");
    let roles: Vec<RoleId> = (0..tin.roles.len())
        .map(|i| {
            // distinct role tags (tag 1 is the TOP-role sentinel; see the
            // preprocess/automata port notes), offset clear of it.
            let mut r = Role::new();
            r.set_role_tag(100 + i as Cint64);
            b.ctx.ontology_arenas_mut().alloc_role(r)
        })
        .collect();
    if std::env::var_os("KM_SAT_ABSORB_DEBUG").is_some() {
        for (index, name) in tin.roles.iter().enumerate() {
            eprintln!("BRIDGE-ROLE tag={} name={name}", 100 + index as Cint64);
        }
        if let Ok(tags) = std::env::var("KM_BRIDGE_NAME_TAGS") {
            let tags: BTreeSet<Cint64> = tags
                .split(',')
                .filter_map(|tag| tag.parse::<Cint64>().ok())
                .collect();
            for (index, name) in tin.concepts.iter().enumerate() {
                let tag = TAG_BASE + index as Cint64;
                if tags.contains(&tag) {
                    eprintln!("BRIDGE-CONCEPT tag={tag} name={name}");
                }
            }
        }
    }
    // Every bridged role gets a wired inverse (both directions, the
    // `inverse_role_propagation` selftest pattern). Needed by the
    // absorption-shape rewrite below: a y-triggered guarded clause
    // `D(y) ∧ R(x,y) → E(x)` encodes as `D ⊑ ∀R⁻.E`.
    let inv_roles: Vec<RoleId> = (0..tin.roles.len())
        .map(|i| {
            let mut r = Role::new();
            r.set_role_tag(100 + (tin.roles.len() + i) as Cint64);
            r.set_inverse_role(roles[i]);
            let id = b.ctx.ontology_arenas_mut().alloc_role(r);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(roles[i])
                .set_inverse_role(id);
            // CSubroleTransformationPreProcess represents inverse equivalence
            // as signed super-role links in both directions. Saturation uses
            // the negative entry to install the successor-to-predecessor
            // propagation link consumed by ALL/AQALL automata.
            b.ctx
                .ontology_arenas_mut()
                .role_mut(roles[i])
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: id,
                    negated: true,
                })
                .add_equivalent_role_linker(super::model::substrate::NegLink {
                    target: id,
                    negated: true,
                });
            b.ctx
                .ontology_arenas_mut()
                .role_mut(id)
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: roles[i],
                    negated: true,
                })
                .add_equivalent_role_linker(super::model::substrate::NegLink {
                    target: roles[i],
                    negated: true,
                });
            id
        })
        .collect();
    let role_inverses: HashMap<RoleId, RoleId> = roles
        .iter()
        .copied()
        .zip(inv_roles.iter().copied())
        .chain(inv_roles.iter().copied().zip(roles.iter().copied()))
        .collect();
    bridge_phase!("inverse-roles");
    // In source-TBox mode Konclude builds the terminology from the normalized
    // class expressions before clausification. The frontend `definers` are a
    // second, clausifier-generated representation of those same expressions;
    // materializing both duplicates the concept DAG and makes every downstream
    // preprocessor visit the duplicate. Keep them only for the legacy clause
    // bridge, where they are the sole structural representation.
    // Resolve internal frontend markers to native signed concepts before
    // building implications. Query concepts remain the atomic `named` vector;
    // only clause literals use `resolved`. Provenance is emitted in dependency
    // order (operand definers before their parent), so one forward pass is
    // sufficient.
    let mut resolved: Vec<(ConceptId, bool)> = named.iter().copied().map(|c| (c, false)).collect();
    if trigger_absorb && !source_mode {
        let concept_index: HashMap<&str, usize> = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let role_index: HashMap<&str, usize> = tin
            .roles
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let card_markers: BTreeSet<usize> = tin.card_defs.iter().map(|d| d.marker).collect();
        for d in &tin.definers {
            let Some(&marker) = concept_index.get(d.marker.as_str()) else {
                continue;
            };
            if card_markers.contains(&marker) {
                continue;
            }
            let operands: Option<Vec<(ConceptId, bool)>> = d
                .operands
                .iter()
                .map(|n| concept_index.get(n.as_str()).map(|&i| resolved[i]))
                .collect();
            let Some(operands) = operands else {
                continue;
            };
            let role = d
                .role
                .as_deref()
                .and_then(|r| role_index.get(r).copied())
                .map(|r| roles[r]);
            let value = match d.kind {
                DefinerKind::Top => {
                    let top = b.ctx.processing_data_box().ontology_top_concept();
                    top.is_some().then_some((top, false))
                }
                DefinerKind::Bottom => Some((b.bottom(), false)),
                DefinerKind::Not if operands.len() == 1 => Some((operands[0].0, !operands[0].1)),
                DefinerKind::And if !operands.is_empty() => Some(b.and_of(&operands)),
                DefinerKind::Or if !operands.is_empty() => Some(b.or_of(&operands)),
                DefinerKind::Exists if operands.len() == 1 && role.is_some() => {
                    Some((b.some(role.unwrap(), operands[0]), false))
                }
                DefinerKind::Forall if operands.len() == 1 && role.is_some() => {
                    Some((b.all(role.unwrap(), operands[0]), false))
                }
                DefinerKind::SelfRestriction if role.is_some() => {
                    Some((b.self_restriction(role.unwrap()), false))
                }
                DefinerKind::NotSelf if role.is_some() => {
                    Some((b.self_restriction(role.unwrap()), true))
                }
                DefinerKind::AtLeast if operands.len() == 1 && role.is_some() => Some((
                    b.atleast_q(role.unwrap(), d.n.unwrap_or(0), operands[0]),
                    false,
                )),
                DefinerKind::AtMost if operands.len() == 1 && role.is_some() => Some((
                    b.atmost_q(role.unwrap(), d.n.unwrap_or(0), operands[0]),
                    false,
                )),
                DefinerKind::Not
                | DefinerKind::And
                | DefinerKind::Or
                | DefinerKind::Exists
                | DefinerKind::Forall
                | DefinerKind::SelfRestriction
                | DefinerKind::NotSelf
                | DefinerKind::AtLeast
                | DefinerKind::AtMost => None,
            };
            if let Some(value) = value {
                resolved[marker] = value;
            }
        }
    }
    bridge_phase!("definers");

    let mut tbox: Vec<ConceptId> = Vec::new();
    // Absorption bookkeeping (attached after the encode loop): an implication
    // with a positive concept trigger hangs off that trigger's concept; the
    // rest go to TOP.
    let mut absorbed_pairs: Vec<(ConceptId, ConceptId)> = Vec::new();
    let mut top_gcis: Vec<ConceptId> = Vec::new();
    let mut trigger_caches = TriggerCaches::default();
    let mut singleton_concepts: Vec<ConceptId> = Vec::new();
    let mut unsupported = 0usize;
    // Diagnostic (KM_BRIDGE_DUMP_UNSUP=N): record the shape of the first N
    // unsupported clauses so the next coverage wave can be scoped.
    let dump_unsup: usize = std::env::var("KM_BRIDGE_DUMP_UNSUP")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut dumped = 0usize;
    let mut dump = |cl: &HtClause, why: &str| {
        if dumped < dump_unsup {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                }
            };
            let b: Vec<String> = cl.body.iter().map(show).collect();
            let h: Vec<String> = cl.head.iter().map(show).collect();
            eprintln!("UNSUP[{why}]: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            dumped += 1;
        }
    };
    // Diagnostic (KM_BRIDGE_DUMP_TOPGCI=N): record the shape of the first N
    // clauses that become TOP-attached GCIs (no positive absorption guard) —
    // these branch on EVERY node and are the disjunction-search cost centre.
    let dump_topgci: usize = std::env::var("KM_BRIDGE_DUMP_TOPGCI")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(0);
    let mut dumped_top = 0usize;
    let topgci_names = &tin.concepts;
    let mut dump_top = |cl: &HtClause, why: &str| {
        if dumped_top < dump_topgci {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!(
                            "{}C{c}:{}({t})",
                            if *neg { "¬" } else { "" },
                            topgci_names.get(*c).map(String::as_str).unwrap_or("?")
                        )
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!(
                            "∃R{r}.{}C{c}:{}({t})",
                            if *neg { "¬" } else { "" },
                            topgci_names.get(*c).map(String::as_str).unwrap_or("?")
                        )
                    }
                }
            };
            let b: Vec<String> = cl.body.iter().map(show).collect();
            let h: Vec<String> = cl.head.iter().map(show).collect();
            eprintln!("TOPGCI[{why}]: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            dumped_top += 1;
        }
    };
    // Structures outside the v1 clause encoder count as unsupported input
    // (card_defs are ENCODED below — first-class ≥n/≤n via the ported
    // CCATLEAST/CCATMOST rules — so they are no longer counted here).
    unsupported += tin.nominals.len();

    // Konclude keeps source ObjectPropertyDomain/ObjectPropertyRange axioms
    // directly on CRole. In source-TBox mode use the converter's explicit
    // RBox provenance: a guarded clause shape is not sufficient, because the
    // clausifier emits the same shape for ordinary class-expression rules.
    // (ORE 9724 has no source domains/ranges but thousands of such rules.)
    if source_mode {
        for &(role, concept) in &tin.role_domains {
            let (Some(&role), Some(&concept)) = (roles.get(role), named.get(concept)) else {
                unsupported += 1;
                continue;
            };
            let inverse = role_inverses[&role];
            let link = super::model::substrate::NegLink {
                target: concept,
                negated: false,
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .domain_linker
                .push(link);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(inverse)
                .range_linker
                .push(link);
        }
        for &(role, concept) in &tin.role_ranges {
            let (Some(&role), Some(&concept)) = (roles.get(role), named.get(concept)) else {
                unsupported += 1;
                continue;
            };
            let inverse = role_inverses[&role];
            let link = super::model::substrate::NegLink {
                target: concept,
                negated: false,
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .range_linker
                .push(link);
            b.ctx
                .ontology_arenas_mut()
                .role_mut(inverse)
                .domain_linker
                .push(link);
        }
    }

    // ---- pass 1: role hierarchy `R(x,y) → S(x,y)` --------------------------
    // Collected first and installed as direct and (transitively closed)
    // indirect-super-role linkers on the sub-role — the exact structures the
    // automata preprocessor, ∀/edge rules, and u08 hierarchy-resolved edge
    // reapply consume (see CSubroleTransformationPreProcess). Konclude seeds
    // every indirect list with the role itself before adding strict supers;
    // collectSubRoleChains relies on that reflexive entry to index a chain
    // under its own super role.
    // The closure runs over BOTH polarities (vertex = 2·role + inverted): a
    // plain `R ⊑ S` also yields `R⁻ ⊑ S⁻` (needed by the mirror inverse-edge
    // installs), and an inverse-hierarchy clause `R(x,y) → S(y,x)` (`R ⊑ S⁻`,
    // the clausal InverseObjectProperties half) crosses polarity. All entries
    // are installed with negated=false against the CONCRETE role object
    // (`roles[·]` / `inv_roles[·]`) — `has_indirect_super_role` (the u08
    // ∀-matcher) ignores the negated flag, so polarity must be resolved to
    // distinct role objects, never encoded in the flag.
    let n_r = tin.roles.len();
    let mut sub_super: Vec<Vec<usize>> = vec![Vec::new(); 2 * n_r];
    let is_hierarchy = |cl: &HtClause| -> Option<(usize, usize)> {
        if cl.body.len() != 1 || cl.head.len() != 1 {
            return None;
        }
        if let (
            HAtom::Role {
                r: sr,
                s: ss,
                t: st,
            },
            HAtom::Role {
                r: hr,
                s: hs,
                t: ht,
            },
        ) = (&cl.body[0], &cl.head[0])
        {
            if ss == hs && st == ht && ss != st && sr != hr {
                return Some((*sr, *hr));
            }
        }
        None
    };
    // `R(x,y) → S(y,x)` — `R ⊑ S⁻`; `sr == hr` allowed (a symmetric role).
    let is_inv_hierarchy = |cl: &HtClause| -> Option<(usize, usize)> {
        if cl.body.len() != 1 || cl.head.len() != 1 {
            return None;
        }
        if let (
            HAtom::Role {
                r: sr,
                s: ss,
                t: st,
            },
            HAtom::Role {
                r: hr,
                s: hs,
                t: ht,
            },
        ) = (&cl.body[0], &cl.head[0])
        {
            if ss == ht && st == hs && ss != st {
                return Some((*sr, *hr));
            }
        }
        None
    };
    for cl in &tin.clauses {
        if let Some((sub, sup)) = is_hierarchy(cl) {
            sub_super[2 * sub].push(2 * sup);
            sub_super[2 * sub + 1].push(2 * sup + 1);
        } else if let Some((sub, sup)) = is_inv_hierarchy(cl) {
            sub_super[2 * sub].push(2 * sup + 1);
            sub_super[2 * sub + 1].push(2 * sup);
        }
    }
    // Direct hierarchy plus reflexive-transitive closure per (role, polarity)
    // vertex (small role counts; DFS).
    for sub in 0..sub_super.len() {
        let sub_obj = if sub % 2 == 0 {
            roles[sub / 2]
        } else {
            inv_roles[sub / 2]
        };
        for &direct in &sub_super[sub] {
            let direct_obj = if direct % 2 == 0 {
                roles[direct / 2]
            } else {
                inv_roles[direct / 2]
            };
            let inverse_direct_obj = if direct % 2 == 0 {
                inv_roles[direct / 2]
            } else {
                roles[direct / 2]
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(sub_obj)
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: direct_obj,
                    negated: false,
                })
                .add_super_role_linker(super::model::substrate::NegLink {
                    target: inverse_direct_obj,
                    negated: true,
                });
        }
        b.ctx
            .ontology_arenas_mut()
            .role_mut(sub_obj)
            .add_indirect_super_role_linker(super::model::substrate::NegLink {
                target: sub_obj,
                negated: false,
            })
            .add_indirect_super_role_linker(super::model::substrate::NegLink {
                target: if sub % 2 == 0 {
                    inv_roles[sub / 2]
                } else {
                    roles[sub / 2]
                },
                negated: true,
            });
        let mut seen: BTreeSet<usize> = BTreeSet::new();
        let mut stack: Vec<usize> = sub_super[sub].clone();
        while let Some(s) = stack.pop() {
            if s != sub && seen.insert(s) {
                stack.extend(sub_super[s].iter().copied());
            }
        }
        for s in seen {
            let sup_obj = if s % 2 == 0 {
                roles[s / 2]
            } else {
                inv_roles[s / 2]
            };
            let inverse_sup_obj = if s % 2 == 0 {
                inv_roles[s / 2]
            } else {
                roles[s / 2]
            };
            b.ctx
                .ontology_arenas_mut()
                .role_mut(sub_obj)
                .add_indirect_super_role_linker(super::model::substrate::NegLink {
                    target: sup_obj,
                    negated: false,
                })
                .add_indirect_super_role_linker(super::model::substrate::NegLink {
                    target: inverse_sup_obj,
                    negated: true,
                });
        }
    }
    bridge_phase!("role-hierarchy");

    // Production RBox: materialize every retained R1 o R2 <= R axiom as the
    // CRoleChain / super-sharing structure consumed by Konclude's role-
    // automata preprocessor. Transitivity is the special chain R o R <= R.
    let mut role_chains: Vec<(usize, usize, usize)> = tin.chains.clone();
    for &role in &tin.transitive {
        role_chains.push((role, role, role));
    }
    role_chains.sort_unstable();
    role_chains.dedup();
    let mut object_chains: Vec<(RoleId, RoleId, RoleId)> = Vec::new();
    for (left, right, super_role) in role_chains {
        if left >= roles.len() || right >= roles.len() || super_role >= roles.len() {
            unsupported += 1;
            continue;
        }
        object_chains.push((roles[left], roles[right], roles[super_role]));
        // The bridge uses concrete inverse role objects. Materialize the
        // reversed chain as well as the signed inverse view so saturation's
        // successor-extension construction has an explicit creation-role
        // path in both directions.
        object_chains.push((inv_roles[right], inv_roles[left], inv_roles[super_role]));
    }
    object_chains.sort_by_key(|(left, right, sup)| (left.raw, right.raw, sup.raw));
    object_chains.dedup();
    for (left, right, super_role) in object_chains {
        let mut chain = RoleChain::new();
        chain
            .append_role_chain_linker(left)
            .append_role_chain_linker(right);
        let chain_id = b.ctx.ontology_arenas_mut().alloc_role_chain(chain);
        b.ctx
            .ontology_arenas_mut()
            .role_chain_mut(chain_id)
            .set_role_chain_tag(chain_id.index() as Cint64);
        b.ctx
            .ontology_arenas_mut()
            .role_mut(super_role)
            .add_role_chain_super_sharing_linker(chain_id);
        let complex_roles: Vec<RoleId> = std::iter::once(super_role)
            .chain(
                b.ctx
                    .ontology_arenas()
                    .role(super_role)
                    .get_indirect_super_role_list()
                    .iter()
                    .map(|link| link.target),
            )
            .collect();
        for role in complex_roles {
            b.ctx
                .ontology_arenas_mut()
                .role_mut(role)
                .set_role_complexity(true);
        }
    }
    bridge_phase!("role-chains");

    // ---- pass 2: functional roles `R(0,1) ∧ R(0,2) → eq(1,2)` --------------
    // The clausal form of `⊤ ⊑ ≤1 R.⊤` (a functional property / global at-most
    // 1). Detected here and later encoded as a `CCATMOST(R, 1)` on TOP so
    // every node enforces ≤1 R-successor through the ported merge rule
    // (`ht_apply_atmost_merge`). The clause itself is then consumed (not
    // unsupported).
    let is_functional = |cl: &HtClause| -> Option<usize> {
        if cl.body.len() != 2 || cl.head.len() != 1 {
            return None;
        }
        let (b0, b1) = (&cl.body[0], &cl.body[1]);
        if let (
            HAtom::Role {
                r: r0,
                s: s0,
                t: t0,
            },
            HAtom::Role {
                r: r1,
                s: s1,
                t: t1,
            },
            HAtom::Eq { s: es, t: et },
        ) = (b0, b1, &cl.head[0])
        {
            // same role, shared source 0, distinct targets, head equates them.
            if r0 == r1 && s0 == s1 && t0 != t1 {
                let (a, b) = (*t0.min(t1), *t0.max(t1));
                let (ea, eb) = (*es.min(et), *es.max(et));
                if (a, b) == (ea, eb) && *s0 != a && *s0 != b {
                    return Some(*r0);
                }
            }
        }
        None
    };
    let mut functional_roles: BTreeSet<usize> = BTreeSet::new();
    for cl in &tin.clauses {
        if let Some(r) = is_functional(cl) {
            functional_roles.insert(r);
        }
    }
    for &role in &functional_roles {
        b.ctx
            .ontology_arenas_mut()
            .role_mut(roles[role])
            .set_functional(true);
    }
    bridge_phase!("functional-scan");

    // Konclude builds the terminology before clausification: named-left
    // inclusions become CCSUB operands and only residual structural-left GCIs
    // reach CTriggeredImplicationBinaryAbsorberPreProcess. Use the normalized
    // source side channel when present, then ignore the frontend's derived
    // concept clauses below (role hierarchy/functionality clauses remain the
    // authoritative RBox representation).
    if source_mode {
        let concept_index: HashMap<&str, usize> = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();
        let role_index: HashMap<&str, usize> = tin
            .roles
            .iter()
            .enumerate()
            .map(|(i, name)| (name.as_str(), i))
            .collect();
        let mut concept_cache = HashMap::new();
        let mut direct = 0usize;
        let mut role_links = 0usize;
        let mut absorbed = 0usize;
        let mut residual = 0usize;
        let mut source_unsupported = 0usize;
        let mut equivalent_definitions = 0usize;
        let mut equivalent_definition_names = Vec::new();
        let mut absorbed_equivalent_definitions = 0usize;
        let mut seen_inclusions = std::collections::HashSet::new();
        let mut forced_subclass_names = std::collections::HashSet::new();
        let mut equivalence_name_counts: HashMap<&str, usize> = HashMap::new();
        for axiom in &tin.source_axioms {
            match axiom.kind {
                crate::json_io::SourceAxiomKind::SubClass => {
                    if let SourceConcept::Name(name) = &axiom.left {
                        forced_subclass_names.insert(name.as_str());
                    }
                }
                crate::json_io::SourceAxiomKind::Disjoint => {
                    for side in [&axiom.left, &axiom.right] {
                        if let SourceConcept::Name(name) = side {
                            forced_subclass_names.insert(name.as_str());
                        }
                    }
                }
                crate::json_io::SourceAxiomKind::Equivalent => {
                    for side in [&axiom.left, &axiom.right] {
                        if let SourceConcept::Name(name) = side {
                            *equivalence_name_counts.entry(name.as_str()).or_default() += 1;
                        }
                    }
                }
            }
        }
        bridge_phase!("source-prescan");
        macro_rules! encode {
            ($left:expr, $right:expr $(,)?) => {{
                let left = $left;
                let right = $right;
                if seen_inclusions.insert((left.clone(), right.clone())) {
                    match encode_source_subclass(
                        &mut b,
                        left,
                        right,
                        &concept_index,
                        &role_index,
                        &named,
                        &roles,
                        &inv_roles,
                        &role_inverses,
                        &mut concept_cache,
                        &mut trigger_caches,
                        &mut tbox,
                        &mut top_gcis,
                    ) {
                        SourceEncoding::Direct => direct += 1,
                        SourceEncoding::RoleLink => role_links += 1,
                        SourceEncoding::AbsorbedGci => absorbed += 1,
                        SourceEncoding::TopGci => residual += 1,
                        SourceEncoding::Unsupported => source_unsupported += 1,
                    }
                }
            }};
        }
        for (axiom_index, axiom) in tin.source_axioms.iter().enumerate() {
            match axiom.kind {
                crate::json_io::SourceAxiomKind::SubClass => {
                    encode!(&axiom.left, &axiom.right);
                }
                crate::json_io::SourceAxiomKind::Equivalent => {
                    // `buildPermutableConceptEquivalentClass` chooses a still
                    // undefined named side for a direct CCEQ definition.
                    let candidate = [(&axiom.left, &axiom.right), (&axiom.right, &axiom.left)]
                        .into_iter()
                        .find_map(|(named_side, definition)| {
                            let SourceConcept::Name(name) = named_side else {
                                return None;
                            };
                            if forced_subclass_names.contains(name.as_str())
                                || equivalence_name_counts.get(name.as_str()) != Some(&1)
                            {
                                return None;
                            }
                            let &index = concept_index.get(name.as_str())?;
                            (b.ctx
                                .ontology_arenas()
                                .concept(named[index])
                                .get_operator_code()
                                == op::CCATOM)
                                .then_some((named[index], definition, name.as_str()))
                        });
                    let defined = candidate.is_some_and(|(host, definition, name)| {
                        let Some(built) = build_source_concept(
                            &mut b,
                            definition,
                            &concept_index,
                            &role_index,
                            &named,
                            &roles,
                            &inv_roles,
                            &mut concept_cache,
                        ) else {
                            return false;
                        };
                        equivalent_definition_names.push(name.to_string());
                        // Port of the absorber's equivalence pre-pass. A fully
                        // triggerable definition is changed CCEQ -> CCSUB and
                        // gets the reverse direction as a binary implication.
                        let triggerable = full_absorption_trigger(
                            &mut b,
                            built,
                            &role_inverses,
                            &mut trigger_caches,
                        )
                        .is_some();
                        if triggerable {
                            let forward = b.add_unfolding(host, built.0, built.1);
                            let reverse = absorb_concept_disjunction(
                                &mut b,
                                &[built],
                                &[(host, false)],
                                &role_inverses,
                                &mut trigger_caches,
                            );
                            if forward && reverse {
                                absorbed_equivalent_definitions += 1;
                                true
                            } else {
                                false
                            }
                        } else {
                            let defined = b.add_equivalent_definition(host, built.0, built.1);
                            if defined {
                                // Exact non-candidate branch of
                                // `CTriggeredImplicationBinaryAbsorberPreProcess`
                                // (cpp 203-215). Konclude either builds the
                                // optional partial-equivalence candidate or
                                // inserts the still-CCEQ host into
                                // `mEquivConNonCandidateSet`. The bridge does
                                // not materialise that optional optimization,
                                // so it takes Konclude's non-candidate branch.
                                b.ctx
                                    .ontology_arenas_mut()
                                    .insert_equivalent_concept_non_candidate(host);
                            }
                            defined
                        }
                    });
                    if defined {
                        equivalent_definitions += 1;
                    } else {
                        encode!(&axiom.left, &axiom.right);
                        encode!(&axiom.right, &axiom.left);
                    }
                }
                crate::json_io::SourceAxiomKind::Disjoint => {
                    encode!(
                        &axiom.left,
                        &SourceConcept::Not(Box::new(axiom.right.clone())),
                    );
                    encode!(
                        &axiom.right,
                        &SourceConcept::Not(Box::new(axiom.left.clone())),
                    );
                }
            }
            if bridge_phase_trace && axiom_index > 0 && axiom_index % 4096 == 0 {
                let now = std::time::Instant::now();
                eprintln!(
                    "BRIDGE-PHASE source-progress axioms={}/{} delta={:.3}s total={:.3}s concepts={}",
                    axiom_index,
                    tin.source_axioms.len(),
                    now.duration_since(bridge_phase_started).as_secs_f64(),
                    now.duration_since(bridge_started).as_secs_f64(),
                    b.ctx.ontology_arenas().concept_count(),
                );
                bridge_phase_started = now;
            }
        }
        bridge_phase!("source-build");
        unsupported += source_unsupported;
        if std::env::var_os("KM_HT_STATS").is_some() {
            eprintln!(
                "bridge [source-tbox] axioms={} eq={}/{} {:?} direct={} role-links={} absorbed-gci={} top-gci={} unsupported={}",
                tin.source_axioms.len(),
                absorbed_equivalent_definitions,
                equivalent_definitions,
                equivalent_definition_names,
                direct,
                role_links,
                absorbed,
                residual,
                source_unsupported
            );
        }
    }

    'clause: for cl in &tin.clauses {
        // hierarchy clauses (plain + inverse) were consumed by pass 1
        if is_hierarchy(cl).is_some() || is_inv_hierarchy(cl).is_some() {
            continue;
        }
        // functional clauses were consumed by pass 2
        if is_functional(cl).is_some() {
            continue;
        }
        // Source class axioms and RBox domain/range axioms have already been
        // installed from their provenance-bearing side channels. Suppress all
        // concept-bearing clausifier copies; their clause shapes cannot tell
        // those two sources apart.
        if source_mode
            && cl
                .body
                .iter()
                .chain(&cl.head)
                .any(|atom| matches!(atom, HAtom::Concept { .. } | HAtom::Exist { .. }))
        {
            continue;
        }
        // ---- classify the clause's variable/role shape -------------------
        let mut body_roles: Vec<(usize, usize, usize)> = Vec::new(); // (r, s, t)
        let mut body_bad = false;
        for a in &cl.body {
            match a {
                HAtom::Role { r, s, t } => body_roles.push((*r, *s, *t)),
                HAtom::Eq { .. } | HAtom::Exist { .. } => {
                    body_bad = true;
                }
                HAtom::Concept { .. } => {}
            }
        }
        if body_bad {
            unsupported += 1;
            dump(cl, "body-eq-or-exist");
            continue 'clause;
        }
        // ---- ≥k-recognition: guards(0) ∧ C(t_i) ∧ R(0,t_i) → D(0)… ∨ all-pairs eq ----
        // `⋀guards ⊓ ≥k R.C ⊑ ⋁D` ⟺ `implication(guards → ⋁D ∨ ≤(k−1) R.C)`:
        // k pairwise-distinct R.C-successors force some D, and the ≤(k−1)
        // qualified at-most (the ported CCATMOST merge rule) carries the
        // eq-head semantics exactly — so the clause is CONSUMED, not
        // unsupported. A shared-TARGET orientation (`R(t_i,0)`, e.g. inverse-
        // functional) encodes on the concrete inverse-role object.
        //
        // Recognition encoding: DEFAULT ON (`KM_HT_BRIDGE_NO_RECOG` opts
        // out). The early "3 spurious onto `Path`" measurement that kept this
        // arm opt-in was NOT this encoding's fault: the answers rode the
        // phantom card-def root re-seed (fixed 84e38bf) and the u29 DDB
        // leftover-poisoning wrong-cancel (fixed 7c521cb). With both fixed,
        // ore_ont_12653 classifies gold-clean (missing=0 spurious=0) with
        // this arm on, and the oracle suite is green in all 6 search-mode
        // combos. Without it every eq-head clause counts unsupported and the
        // production driver declines whole recognition-family ontologies.
        if !body_roles.is_empty()
            && cl.head.iter().any(|a| matches!(a, HAtom::Eq { .. }))
            && std::env::var_os("KM_HT_BRIDGE_NO_RECOG").is_none()
        {
            let recog = (|| -> Option<(RoleId, usize, Option<usize>, Vec<(usize, bool)>, Vec<usize>, usize)> {
                let r0 = body_roles[0].0;
                if body_roles.iter().any(|&(r, _, _)| r != r0) {
                    return None;
                }
                // orientation: all roles share the source var (hub) or all
                // share the target var (inverse orientation).
                let (role_obj, hub, mut targets): (RoleId, usize, Vec<usize>) =
                    if body_roles.iter().all(|&(_, s, _)| s == body_roles[0].1) {
                        (roles[r0], body_roles[0].1, body_roles.iter().map(|&(_, _, t)| t).collect())
                    } else if body_roles.iter().all(|&(_, _, t)| t == body_roles[0].2) {
                        (inv_roles[r0], body_roles[0].2, body_roles.iter().map(|&(_, s, _)| s).collect())
                    } else {
                        return None;
                    };
                targets.sort_unstable();
                let k = targets.len();
                if k < 2 {
                    return None;
                }
                targets.dedup();
                if targets.len() != k || targets.contains(&hub) {
                    return None;
                }
                let mut guards: Vec<(usize, bool)> = Vec::new();
                let mut per_target: HashMap<usize, Vec<usize>> = HashMap::new();
                for a in &cl.body {
                    if let HAtom::Concept { neg, c, t } = a {
                        if *t == hub {
                            guards.push((*c, *neg));
                        } else if targets.binary_search(t).is_ok() {
                            if *neg {
                                return None;
                            }
                            per_target.entry(*t).or_default().push(*c);
                        } else {
                            return None;
                        }
                    }
                }
                // the qualifier: the SAME (≤1-element) positive concept list
                // on every successor variable.
                let mut qual: Option<Vec<usize>> = None;
                for t in &targets {
                    let mut v = per_target.remove(t).unwrap_or_default();
                    v.sort_unstable();
                    match &qual {
                        None => qual = Some(v),
                        Some(q) if *q == v => {}
                        _ => return None,
                    }
                }
                let qual = qual.unwrap_or_default();
                if qual.len() > 1 {
                    return None;
                }
                let mut heads: Vec<usize> = Vec::new();
                let mut eqs: BTreeSet<(usize, usize)> = BTreeSet::new();
                for a in &cl.head {
                    match a {
                        HAtom::Concept { neg, c, t } => {
                            if *neg || *t != hub {
                                return None;
                            }
                            heads.push(*c);
                        }
                        HAtom::Eq { s, t } => {
                            eqs.insert((*s.min(t), *s.max(t)));
                        }
                        _ => return None,
                    }
                }
                let mut want: BTreeSet<(usize, usize)> = BTreeSet::new();
                for i in 0..k {
                    for j in (i + 1)..k {
                        want.insert((targets[i], targets[j]));
                    }
                }
                if eqs != want {
                    return None;
                }
                Some((role_obj, k, qual.first().copied(), guards, heads, r0))
            })();
            if let Some((role_obj, k, qual, guards, heads, _r0)) = recog {
                // KM_BRIDGE_DUMP_RECOG: print each recognized ≥k clause's
                // encoding parameters (spurious-subsumption hunts).
                if std::env::var_os("KM_BRIDGE_DUMP_RECOG").is_some() {
                    eprintln!(
                        "RECOG r={_r0} k={k} qual={qual:?} guards={guards:?} heads={heads:?} ({})",
                        if guards.is_empty() {
                            "TOP-ATTACHED"
                        } else {
                            "absorbed"
                        }
                    );
                }
                let am = match qual {
                    Some(c) => b.atmost_q(role_obj, (k - 1) as Cint64, resolved[c]),
                    None => b.atmost(role_obj, (k - 1) as Cint64),
                };
                let mut head_ops: Vec<(ConceptId, bool)> = heads
                    .iter()
                    .map(|&c| {
                        if trigger_absorb {
                            resolved[c]
                        } else {
                            (named[c], false)
                        }
                    })
                    .collect();
                head_ops.push((am, false));
                if trigger_absorb {
                    let body_ops: Vec<(ConceptId, bool)> = guards
                        .iter()
                        .map(|&(c, negated)| (resolved[c].0, resolved[c].1 ^ negated))
                        .collect();
                    if absorb_concept_disjunction(
                        &mut b,
                        &body_ops,
                        &head_ops,
                        &role_inverses,
                        &mut trigger_caches,
                    ) {
                        continue 'clause;
                    }
                }
                let head = b.or_of(&head_ops);
                let triggers: Vec<(ConceptId, bool)> =
                    guards.iter().map(|&(c, n)| (named[c], n)).collect();
                let imp = b.implication(head, &triggers);
                tbox.push(imp);
                match triggers.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "recog");
                        top_gcis.push(imp)
                    }
                }
                continue 'clause;
            }
        }
        // ---- singleton-concept recognition: `C(v1) ∧ C(v2) → v1 = v2` ------
        // The clausal datatype value-identity shape (a literal value is one
        // semantic object, so any two carriers of `__dt__val__…` are equal;
        // Konclude gets this natively from its databox literal handling, the
        // clausal frontend surfaces it role-free). CONSUMED as a singleton
        // registration: the kernel's deterministic scan-at-fixpoint merge
        // (u02 `ht_apply_singleton_merges`) realises the eq head exactly —
        // deterministic (single-disjunct head), no branch point. General
        // structural rule: any concept in this shape is a singleton.
        // KM_HT_NO_SINGLETON: diagnostic A/B gate — count the shape
        // unsupported instead (the pre-d58c2b2 behaviour: the driver then
        // DECLINES, isolating the merge rule's effect on spuriousness).
        if body_roles.is_empty()
            && cl.body.len() == 2
            && cl.head.len() == 1
            && std::env::var_os("KM_HT_NO_SINGLETON").is_none()
        {
            if let (
                HAtom::Concept {
                    neg: false,
                    c: c0,
                    t: t0,
                },
                HAtom::Concept {
                    neg: false,
                    c: c1,
                    t: t1,
                },
                HAtom::Eq { s: es, t: et },
            ) = (&cl.body[0], &cl.body[1], &cl.head[0])
            {
                if c0 == c1 && t0 != t1 {
                    let (a, bb) = (*t0.min(t1), *t0.max(t1));
                    let (ea, eb) = (*es.min(et), *es.max(et));
                    if (a, bb) == (ea, eb) {
                        let sc = named[*c0];
                        if !singleton_concepts.contains(&sc) {
                            singleton_concepts.push(sc);
                        }
                        continue 'clause;
                    }
                }
            }
        }
        if cl
            .head
            .iter()
            .any(|a| matches!(a, HAtom::Role { .. } | HAtom::Eq { .. }))
        {
            unsupported += 1;
            dump(cl, "head-role-or-eq");
            continue 'clause;
        }
        let vars: BTreeSet<usize> = cl
            .body
            .iter()
            .chain(cl.head.iter())
            .flat_map(|a| match a {
                HAtom::Concept { t, .. } | HAtom::Exist { t, .. } => vec![*t],
                HAtom::Role { s, t, .. } => vec![*s, *t],
                HAtom::Eq { s, t } => vec![*s, *t],
            })
            .collect();

        // literal → (concept, negated), positively as written
        let lit = |b: &mut Builder, a: &HAtom| -> (ConceptId, bool) {
            match a {
                HAtom::Concept { neg, c, .. } => (named[*c], *neg),
                HAtom::Exist { r, neg, c, .. } => {
                    let filler = (named[*c], *neg);
                    (b.some(roles[*r], filler), false)
                }
                _ => unreachable!("filtered above"),
            }
        };

        if body_roles.is_empty() && vars.iter().all(|&v| v == 0) {
            // ---- pure concept clause over the root variable --------------
            if trigger_absorb {
                let body_ops: Vec<(ConceptId, bool)> = cl
                    .body
                    .iter()
                    .map(|a| match a {
                        HAtom::Concept { neg, c, .. } => (resolved[*c].0, resolved[*c].1 ^ *neg),
                        _ => unreachable!("role/eq bodies filtered"),
                    })
                    .collect();
                let mut head_ops = Vec::new();
                for a in &cl.head {
                    match a {
                        HAtom::Concept { neg, c, .. } => {
                            head_ops.push((resolved[*c].0, resolved[*c].1 ^ *neg));
                        }
                        HAtom::Exist { r, neg, c, .. } => {
                            let filler = (resolved[*c].0, resolved[*c].1 ^ *neg);
                            head_ops.push((b.some(roles[*r], filler), false));
                        }
                        _ => unreachable!("role/eq heads filtered"),
                    }
                }

                // Konclude `asorbForallsToRanges`: TOP -> ALL R.C is stored on
                // the role and removed from TOP after GCI absorption.
                if body_ops.is_empty() && head_ops.len() == 1 && !head_ops[0].1 {
                    let (op_code, role, operands) = {
                        let c = b.ctx.ontology_arenas().concept(head_ops[0].0);
                        (
                            c.get_operator_code(),
                            c.get_role(),
                            c.get_operand_list().to_vec(),
                        )
                    };
                    if op_code == op::CCTOP {
                        continue 'clause;
                    }
                    if op_code == op::CCALL && operands.len() == 1 {
                        let link = operands[0];
                        b.ctx
                            .ontology_arenas_mut()
                            .role_mut(role)
                            .range_linker
                            .push(link);
                        if let Some(&inverse) = role_inverses.get(&role) {
                            b.ctx
                                .ontology_arenas_mut()
                                .role_mut(inverse)
                                .domain_linker
                                .push(link);
                        }
                        continue 'clause;
                    }
                }

                if absorb_concept_disjunction(
                    &mut b,
                    &body_ops,
                    &head_ops,
                    &role_inverses,
                    &mut trigger_caches,
                ) {
                    continue 'clause;
                }
            }
            let raw_triggers: Vec<(ConceptId, bool)> = cl
                .body
                .iter()
                .map(|a| match a {
                    HAtom::Concept { neg, c, .. } => (named[*c], *neg),
                    _ => unreachable!("role/eq bodies filtered"),
                })
                .collect();
            let raw_heads: Vec<(ConceptId, bool)> =
                cl.head.iter().map(|a| lit(&mut b, a)).collect();
            let mut triggers = Vec::new();
            let mut heads = Vec::new();
            for (c, neg) in raw_triggers {
                if neg {
                    heads.push((c, false));
                } else {
                    triggers.push((c, false));
                }
            }
            for (c, neg) in raw_heads {
                if neg {
                    triggers.push((c, false));
                } else {
                    heads.push((c, false));
                }
            }
            triggers.sort_by_key(|(c, n)| (c.raw, *n));
            triggers.dedup();
            heads.sort_by_key(|(c, n)| (c.raw, *n));
            heads.dedup();
            let opposite =
                |ops: &[(ConceptId, bool)]| ops.iter().any(|&(c, n)| ops.contains(&(c, !n)));
            if opposite(&triggers)
                || opposite(&heads)
                || triggers.iter().any(|lit| heads.contains(lit))
            {
                continue 'clause;
            }
            let head = if heads.is_empty() {
                (b.bottom(), false)
            } else {
                b.or_of(&heads)
            };
            let imp = b.implication(head, &triggers);
            tbox.push(imp);
            match triggers.iter().find(|&&(_, neg)| !neg) {
                Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                None => {
                    dump_top(cl, "pure-concept");
                    top_gcis.push(imp)
                }
            }
            continue;
        }

        if body_roles.len() == 1 {
            // ---- guarded two-variable clause: R(x, y) --------------------
            let (r, s, t) = body_roles[0];
            if s != 0 || t == 0 || vars.iter().any(|&v| v != s && v != t) {
                unsupported += 1;
                dump(cl, "guarded-var-shape");
                continue;
            }
            let _ = r;
            let mut triggers: Vec<(ConceptId, bool)> = Vec::new(); // at x
            let mut succ_body: Vec<(ConceptId, bool)> = Vec::new(); // at y
            for a in &cl.body {
                if let HAtom::Concept { neg, c, t: at } = a {
                    if *at == 0 {
                        triggers.push((named[*c], *neg));
                    } else {
                        succ_body.push((named[*c], *neg));
                    }
                }
            }
            let mut head_x: Vec<(ConceptId, bool)> = Vec::new();
            let mut head_y: Vec<(ConceptId, bool)> = Vec::new();
            for a in &cl.head {
                let at = match a {
                    HAtom::Concept { t, .. } | HAtom::Exist { t, .. } => *t,
                    _ => unreachable!("filtered above"),
                };
                if at == 0 {
                    head_x.push(lit(&mut b, a));
                } else if matches!(a, HAtom::Exist { .. }) {
                    // nested ∃ under the ∀ — out of the v1 fragment
                    unsupported += 1;
                    dump(cl, "nested-exist-under-forall");
                    continue 'clause;
                } else {
                    head_y.push(lit(&mut b, a));
                }
            }
            let mut norm_triggers = Vec::new();
            let mut norm_head_x = Vec::new();
            for (c, neg) in triggers.drain(..) {
                if neg {
                    norm_head_x.push((c, false));
                } else {
                    norm_triggers.push((c, false));
                }
            }
            for (c, neg) in head_x.drain(..) {
                if neg {
                    norm_triggers.push((c, false));
                } else {
                    norm_head_x.push((c, false));
                }
            }
            triggers = norm_triggers;
            head_x = norm_head_x;

            let mut norm_succ_body = Vec::new();
            let mut norm_head_y = Vec::new();
            for (c, neg) in succ_body.drain(..) {
                if neg {
                    norm_head_y.push((c, false));
                } else {
                    norm_succ_body.push((c, false));
                }
            }
            for (c, neg) in head_y.drain(..) {
                if neg {
                    norm_succ_body.push((c, false));
                } else {
                    norm_head_y.push((c, false));
                }
            }
            succ_body = norm_succ_body;
            head_y = norm_head_y;
            if !triggers.is_empty() {
                // ---- x-triggered: C ⊑ … ∨ ∀R.(¬D ∨ …) ---------------------
                // ∀R.( ¬D1 ∨ … ∨ F1 ∨ … ) — the y-side residue
                let mut y_ops: Vec<(ConceptId, bool)> = succ_body
                    .iter()
                    .map(|&(c, n)| (c, !n)) // body atoms flip polarity
                    .collect();
                y_ops.extend(head_y.iter().copied());
                let y_disj = if y_ops.is_empty() {
                    (b.bottom(), false)
                } else {
                    b.or_of(&y_ops)
                };
                let all = (b.all(roles[r], y_disj), false);
                // KM_BRIDGE_DUMP_FORALL=<role_idx>: print the antecedent
                // (trigger tags) of every ∀<role>.… implication built here —
                // reveals whether a ∀ is concept-gated or global (all-negative
                // triggers ⇒ TOP-attached ⇒ fires on every node).
                if std::env::var("KM_BRIDGE_DUMP_FORALL")
                    .ok()
                    .and_then(|s| s.parse::<usize>().ok())
                    == Some(r)
                {
                    let tt: Vec<String> = triggers
                        .iter()
                        .map(|&(c, n)| {
                            format!(
                                "{}{}",
                                if n { "¬" } else { "" },
                                b.ctx.ontology_arenas().concept(c).get_concept_tag()
                            )
                        })
                        .collect();
                    let ft: Vec<String> = y_ops
                        .iter()
                        .map(|&(c, n)| {
                            format!(
                                "{}{}",
                                if n { "¬" } else { "" },
                                b.ctx.ontology_arenas().concept(c).get_concept_tag()
                            )
                        })
                        .collect();
                    let global = triggers.iter().all(|&(_, n)| n);
                    eprintln!(
                        "DUMP-FORALL role={r} triggers=[{}] fillers=[{}] GLOBAL={global}",
                        tt.join(" "),
                        ft.join(" ")
                    );
                }
                let head = if head_x.is_empty() {
                    all
                } else {
                    let mut ops = head_x;
                    ops.push(all);
                    b.or_of(&ops)
                };
                let imp = b.implication(head, &triggers);
                tbox.push(imp);
                match triggers.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "forall-residue");
                        top_gcis.push(imp)
                    }
                }
            } else if !succ_body.is_empty() {
                // ---- y-triggered (the absorption shape): ------------------
                // `D(y) ∧ R(x,y) → E(x) ∨ F(y)`  ≡  `D ⊑ F ∨ ∀R⁻.E`
                // (the cb_to_ht definer RECOGNITION direction). Encoded
                // trigger-less it would be a covering disjunction branching
                // on EVERY node (measured: unbounded successor chains); the
                // inverse-∀ form fires only on D-nodes and rides the ported
                // inverse-edge propagation (`inverse_role_propagation`
                // selftest). Konclude reaches the same behaviour through
                // absorption's backward implication triggers.
                let x_disj = if head_x.is_empty() {
                    (b.bottom(), false)
                } else {
                    b.or_of(&head_x)
                };
                let all_inv = (b.all(inv_roles[r], x_disj), false);
                let head = if head_y.is_empty() {
                    all_inv
                } else {
                    let mut ops = head_y;
                    ops.push(all_inv);
                    b.or_of(&ops)
                };
                let imp = b.implication(head, &succ_body);
                tbox.push(imp);
                match succ_body.iter().find(|&&(_, neg)| !neg) {
                    Some(&(host, _)) => absorbed_pairs.push((host, imp)),
                    None => {
                        dump_top(cl, "inv-forall-residue");
                        top_gcis.push(imp)
                    }
                }
            } else if head_y.is_empty() && !head_x.is_empty() {
                // ---- domain axiom `R(x,y) → C(x) [∨ D(x) …]` ----------------
                // Konclude stores these on the role (CRole::domainLinker) and
                // applies them at every link install
                // (createNewIndividualsLink* cpp 22382–22395, ported in u08
                // ht_apply_role_domain_range) — node-count-independent, no
                // covering disjunction needed.
                let (c, neg) = b.or_of(&head_x);
                let nl = super::model::substrate::NegLink {
                    target: c,
                    negated: neg,
                };
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(roles[r])
                    .domain_linker
                    .push(nl);
                // domain(R) = range(R⁻): keep the inverse object consistent so
                // whichever edge direction is installed applies the concept.
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inv_roles[r])
                    .range_linker
                    .push(nl);
            } else if head_x.is_empty() && !head_y.is_empty() {
                // ---- range axiom `R(x,y) → C(y) [∨ D(y) …]` -----------------
                let (c, neg) = b.or_of(&head_y);
                let nl = super::model::substrate::NegLink {
                    target: c,
                    negated: neg,
                };
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(roles[r])
                    .range_linker
                    .push(nl);
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inv_roles[r])
                    .domain_linker
                    .push(nl);
            } else if head_x.is_empty() && head_y.is_empty() {
                // ---- `R(x,y) → ⊥` (empty role): domain ⊥ — any R-edge
                // immediately clashes its source, exactly the axiom's force.
                let bot = b.bottom();
                let nl = super::model::substrate::NegLink {
                    target: bot,
                    negated: false,
                };
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(roles[r])
                    .domain_linker
                    .push(nl);
                b.ctx
                    .ontology_arenas_mut()
                    .role_mut(inv_roles[r])
                    .range_linker
                    .push(nl);
            } else {
                // mixed x/y disjunctive head over an edge with no concept
                // trigger (`R(x,y) → C(x) ∨ D(y)`) — out of the v1 fragment
                // (needs the covering-disjunction machinery Konclude gets from
                // absorption + branch triggers).
                unsupported += 1;
                dump(cl, "edge-no-concept-trigger");
            }
            continue;
        }

        if trigger_absorb
            && body_roles.len() > 1
            && absorb_role_tree_clause(
                &mut b,
                cl,
                &resolved,
                &roles,
                &inv_roles,
                &role_inverses,
                &mut trigger_caches,
            )
        {
            continue 'clause;
        }
        unsupported += 1;
        dump(cl, "multi-role-body");
    }
    bridge_phase!("clause-scan");

    // ---- functional roles → `≤1 R` on TOP (every node) ---------------------
    // Emitted while the Builder still holds the arena borrow. Each functional
    // role R contributes an unqualified `CCATMOST(R, 1)`; attaching it to TOP
    // makes every node enforce ≤1 R-successor via the ported merge rule. The
    // atmost is also seeded on the root each drive pass (it is a universal
    // constraint, not trigger-gated).
    let functional_count = functional_roles.len();
    let atmost_concepts: Vec<ConceptId> = functional_roles
        .iter()
        .map(|&r| b.atmost(roles[r], 1))
        .collect();
    for &a in &atmost_concepts {
        tbox.push(a);
        top_gcis.push(a);
    }

    // ---- first-class number restrictions (KM_HT_CARD `card_defs`) ----------
    // `marker ⊑ ≥n role.filler` / `marker ⊑ ≤n role.filler`, resolved to the
    // ported CCATLEAST / (qualified) CCATMOST concepts and hung off the
    // marker's absorption (CCSUB → AND rule asserts the restriction exactly
    // on marker-labelled nodes). The clausal `⋁ eq` pigeonhole for each
    // marker was already dropped by `cb_to_ht::convert(card_enabled=true)`.
    // NOT in `tbox`: the root re-seed loop dispatches every tbox concept on
    // the probe root QUEUE-ONLY (no label add). Implications self-gate on
    // their retained trigger linkers, but a raw CCATLEAST/CCATMOST enforces
    // UNCONDITIONALLY — seeding it applied the marker's number restriction
    // to every probe subject (measured: covering_atmost_cross_merge_sat,
    // the guard-less `≤2 r.E` armed on the root at branch depth 0 refuted
    // the SAT covering branch). The restriction reaches exactly the
    // marker-labelled nodes through the absorption unfold below.
    for cd in tin.card_defs.iter().filter(|_| !source_mode) {
        let filler = resolved[cd.filler];
        let c = if cd.min {
            b.atleast_q(roles[cd.role], cd.n as Cint64, filler)
        } else {
            b.atmost_q(roles[cd.role], cd.n as Cint64, filler)
        };
        absorbed_pairs.push((named[cd.marker], c));
    }

    // ---- attachment pass: absorption wiring (Konclude's CCSUB mechanism) ---
    // An implication with a positive concept trigger is attached as an
    // operand of that trigger's concept, whose opcode is promoted CCATOM →
    // CCSUB: positive CCSUB dispatches to the AND rule (mPosJumpFuncVec[CCSUB]
    // = applyANDRule; negated CCSUB is atomaric), so the implication is
    // unfolded ONLY in nodes whose label actually contains the trigger —
    // node-count-independent, exactly how absorbed GCIs hang off named
    // concepts in Konclude. This is what keeps per-node work flat: without it
    // every node scanned the whole TBox through TOP (measured on ore_ont_1016:
    // 388 nodes × 13k TOP impls = the 5M drive cap). Restricting assertion to
    // trigger-nodes is sound AND complete (in a trigger-free node the clause
    // is vacuous — the standard absorption argument; DL-clause bodies are
    // positive atoms). The retained ¬trigger linker inside the CCIMPL is then
    // trivially satisfied at unfold time and the remaining triggers ride the
    // condensed reapply queue (install-to-trigger).
    for &(host, imp) in &absorbed_pairs {
        let op_code = b.ctx.ontology_arenas().concept(host).get_operator_code();
        if !matches!(op_code, op::CCATOM | op::CCSUB | op::CCIMPLTRIG) {
            // Never mutate a restriction's operand list into an unfolding list.
            // This guard is the bridge equivalent of Konclude's
            // `addUnfoldingConceptForConcept` operator check.
            tbox.push(imp);
            top_gcis.push(imp);
            continue;
        }
        let c = b.ctx.ontology_arenas_mut().concept_mut(host);
        if op_code == op::CCATOM {
            c.set_operator_code(op::CCSUB);
        }
        c.add_operand_linker(imp, false);
        c.inc_operand_count(1);
    }
    bridge_phase!("attachments");

    // Trigger-less implications go to the ontology TOP concept (Konclude's
    // universal-constraint attachment): `CCTOP` dispatches to the AND rule,
    // and `create_new_individual` labels every fresh successor with TOP — so
    // these reach EVERY node. The probe driver still re-seeds the FULL tbox
    // list on the ROOT each pass (root nodes are not created through
    // `create_new_individual`, so they never receive TOP; the re-drive also
    // remains the cross-drive safety net).
    let top = b.ctx.processing_data_box().ontology_top_concept();
    if top.is_some() {
        let n = top_gcis.len() as i64;
        let top_concept = b.ctx.ontology_arenas_mut().concept_mut(top);
        for &g in &top_gcis {
            top_concept.add_operand_linker(g, false);
        }
        let count = top_concept.get_operand_count();
        top_concept.set_operand_count(count + n);
    }

    // Konclude's common-disjunct extraction feeds CReplacementData read by
    // initializeORProcessing.  The implication-replacement producer requires
    // Konclude's negative trigger-propagation substrate as well; it remains
    // disabled until that producer-to-trigger slice is complete.
    let common_disjunct_replacement_count = extract_common_disjunct_replacements(b.ctx);
    bridge_phase!("common-disjuncts");
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!(
            "bridge [or-replacements] implications=0 common={common_disjunct_replacement_count}"
        );
    }

    // Konclude runs this production preprocessor after the RBox and TBox are
    // built. It rewrites complex-role restrictions to AQCHOOSE/AQAND/AQALL
    // automata consumed by the ported completion and saturation rules.
    RoleChainAutomataTransformationPreProcess::new().preprocess(ctx.ontology_arenas_mut());
    bridge_phase!("role-automata");

    // Konclude's branch-trigger extractor runs after the terminology role
    // transformations. Installing its domain markers earlier would make the
    // automata pass incorrectly translate the diagnostic trigger concepts.
    let next_tag = (0..ctx.ontology_arenas().concept_count())
        .map(|index| {
            ctx.ontology_arenas()
                .concept(ConceptId::new(index as Cint64))
                .get_concept_tag()
        })
        .max()
        .unwrap_or(TAG_BASE)
        + 1;
    let branch_role_trigger_count = {
        let mut builder = Builder { ctx, next_tag };
        install_branch_role_domain_triggers(&mut builder, &mut trigger_caches)
    };
    bridge_phase!("branch-triggers");
    if std::env::var_os("KM_HT_STATS").is_some() {
        eprintln!("bridge [branch-triggers] role-markers={branch_role_trigger_count}");
    }

    // KONCLUDE-PORT-NOTE[terminology]: in Konclude every TBox concept carries
    // its owning CTerminology; several guards key on `getTerminology() !=
    // nullptr` — notably u22's unsat-cache write validation, which REJECTS
    // descriptors of terminology-less concepts (meant to exclude fresh
    // query/nominal concepts whose semantics are not ontology-stable).
    // Bridged concepts ARE the ontology (a deterministic function of `tin`,
    // stable across probes), so stamp them all — without this the unsat
    // cache silently never writes a line (measured on ore_ont_12653:
    // 0 written / 0 hits). The sweep covers every builder helper plus the
    // caller-created TOP.
    {
        let arenas = ctx.ontology_arenas_mut();
        let n = arenas.concept_count();
        for i in 0..n {
            arenas
                .concept_mut(ConceptId::new(i as Cint64))
                .set_terminology(1);
        }
    }
    bridge_phase!("terminology-stamp");

    let _ = functional_count;
    Bridged {
        named,
        roles,
        tbox,
        unsupported,
        absorbed: absorbed_pairs.len(),
        top_attached: top_gcis.len(),
        singleton_concepts,
        source_tbox: source_mode,
    }
}

// ---------------------------------------------------------------------------
// Probe driver — the classify_test re-drive harness over a bridged TBox.
// ---------------------------------------------------------------------------

/// Konclude's DEFAULT blocking configuration for a probe algorithm — the
/// cpp-constructor (115-118, 157) + `readCalculationConfig` default branch
/// (u31): optimized subset blocking searched through the anywhere linked
/// candidate hash, with lazy exact hashing; `saveCoreBlockingConceptsCandidates`
/// is coupled to the linked search (cpp 741). Without a blocking search the
/// completion NEVER blocks (`get_blocking_individual_node` returns NONE when
/// every search flag is off) and any ∃-cycle or DAG-unrolled successor tree
/// runs into the drive cap — measured on ore_ont_1016's Abdomen probe.
pub fn configure_default_blocking(algo: &mut CompletionTaskHandleAlgorithm) {
    // KM_HT_DDB: opt-in dependency-directed backjumping (Konclude's
    // `clashedBacktracking`, u29). Turns the dependency spine ON (every rule
    // application then materializes its dependency node + track point, exactly
    // Konclude's default) and routes clashes through the tracked-clash analysis
    // so the in-process OR backtrack can SKIP branch points the clash does not
    // depend on. Target: the 541 family (deep chronological thrashing).
    if std::env::var_os("KM_HT_DDB").is_some() {
        algo.conf_build_dependencies = true;
        algo.conf_dependency_backjumping = true;
        // Konclude production defaults (CReasonerConfigurationGroup):
        // SemanticBranching=false, AtomicSemanticBranching=true — a new
        // alternative asserts the negation of every previously refuted ATOMIC
        // disjunct, so sibling subtrees cannot re-explore failed disjuncts.
        // KM_HT_NO_SEMB: diagnostic opt-out to isolate its effect on the
        // search shape (541: node growth appeared with semb on).
        if std::env::var_os("KM_HT_NO_SEMB").is_none() {
            algo.conf_atomic_semantic_branching = true;
        }
    }
    // Complete-state restore per alternative via arena journals. The per-node
    // localization landed
    // 2026-07-09: the heavy per-node satellites (label sets, processing
    // queues) are Arc-COW in the process context — a journal save is an O(1)
    // Arc clone and the deep copy happens only for objects the alternative
    // actually writes (Konclude's task-fork copy-on-first-write shape). That
    // removed the uniform-journal whale (12653 DDB classify 0.9s → 260s was
    // the old cost), but COW remains NON-default: measured 2026-07-09
    // (cowddb-48445184), 12653's probes under COW and under COW+DDB both
    // exceed 600s where plain DEFERS in 10s — with complete restores the
    // search must genuinely explore the alternatives that plain-mode
    // leftovers (unsoundly, hence the poison discipline) prune, so the
    // residual gap was SEARCH VOLUME in the old post-clausal terminology. The
    // source-level absorber removes that generated search space; complete COW
    // is therefore the default under KM_TRIGGER_ABSORB and is required for
    // sound sibling isolation (PathOfLength4 in ore_ont_12653 is the oracle).
    // KM_HT_COW also enables it independently; KM_NO_TRIGGER_COW is diagnostic.
    if std::env::var_os("KM_HT_COW").is_some()
        || (std::env::var_os("KM_TRIGGER_ABSORB").is_some()
            && std::env::var_os("KM_NO_TRIGGER_COW").is_none())
    {
        algo.conf_inprocess_cow = true;
    }
    // KM_HT_UNSATCACHE (opt-in, composable with DDB/COW): Konclude's
    // unsatisfiable-cache LEARNING — the search-volume lever the 2026-07-09
    // COW+DDB measurement demands. The write side is u29's clashedBacktracking
    // (`writeClashDescriptorsToCache`, cpp 6844/7009/7056/7332 — already
    // ported and called; it no-ops without an installed handler), validated by
    // u22's guards (single node level, terminology concepts only, no nominals,
    // no atomic clash) so an entry is a self-contained label subset that is
    // unsatisfiable wrt the TBox — a learned nogood, valid across probes. The
    // read side is `testIndividualNodeUnsatisfiableCached` (u21, cpp
    // 4363–4392) probed at Konclude's rule points (OR disjunct addition,
    // SOME/ATLEAST successor generation, at-most init/merge — the constant
    // `CGenerativeNonDeterministicUnsatisfiableCacheRetrievalStrategy`).
    // Konclude runs both ON by default (u31 cpp 604–697). The write side only
    // fires inside DDB's tracked-clash analysis, so this is inert without
    // KM_HT_DDB; the intended production combo is COW+DDB+UNSATCACHE.
    if std::env::var_os("KM_HT_UNSATCACHE").is_some() {
        algo.conf_write_unsat_caching = true;
        algo.conf_test_occur_unsat_cached = true;
    }
    // KM_BRIDGE_NO_BLOCKING: diagnostic knob — run the probe with blocking OFF
    // (∃-cycles then hit the drive cap ⇒ Stop/None). If a verdict that flips
    // WITH blocking becomes stable WITHOUT it, the blocking establish/review
    // path is the order-sensitive mechanism.
    if std::env::var_os("KM_BRIDGE_NO_BLOCKING").is_some() {
        return;
    }
    algo.conf_optimized_sub_set_blocking = true;
    algo.conf_anywhere_blocking_linked_candidate_hash_search = true;
    algo.conf_anywhere_blocking_lazy_exact_hashing = true;
    algo.conf_save_core_blocking_concepts_candidates = true;
}

/// Seed `concept` onto `root`'s concept-processing queue at the immediate
/// priority (8) — the classify_test `seed_concept_on_queue`.
fn seed_concept_on_queue(
    ctx: &mut CalculationAlgorithmContextBase,
    root: NodeId,
    concept: ConceptId,
) {
    // TBox seeds carry the INDEPENDENT base dependency track point (Konclude:
    // base assertions are never untracked; an untracked descriptor is a
    // tracking ERROR that aborts the whole clashedBacktracking analysis).
    let base_tp = ctx.get_or_create_base_dependency_track_point();
    let queue = ctx
        .process_context_mut()
        .node_concept_processing_queue(root, true);
    let con_des = ctx
        .process_context_mut()
        .alloc_con_desc(ConceptDescriptor::new());
    {
        let cd = ctx.process_context_mut().con_desc_mut(con_des);
        cd.concept = concept;
        cd.dep_track_point = base_tp;
    }
    let mut cpd_val = ConceptProcessDescriptor::new();
    cpd_val.concept_des = con_des;
    cpd_val.priority = ConceptProcessPriority::new(8.0);
    cpd_val.dep_track_point = base_tp;
    let cpd = ctx.process_context_mut().alloc_con_proc_desc(cpd_val);
    ConceptProcessingQueue::insert_concept_process_descriptor(
        queue,
        cpd,
        ctx.process_context_mut(),
    );
}

/// A per-probe root/verdict driver over a bridged TBox. `seeds` are the probe
/// concepts (e.g. `[(A, false), (B, true)]` for the `A ⊑ B` unsat test).
/// Returns `Some(true)` iff the probe is UNSATISFIABLE (a genuine Clash),
/// `Some(false)` iff a saturated fixpoint was reached with no clash, and
/// `None` if the drive raised a STOP (e.g. the iteration safety cap) — an
/// UNKNOWN verdict a caller must never fold into either answer.
///
/// Mirrors `classify_test::is_unsatisfiable`: re-seeds the TBox implications
/// each pass (the stand-in for the unported condensed reapply queue) and
/// breaks only on a stable concept count with NO disjunction backtrack in the
/// pass (see `or_backtrack_count`).
pub fn bridged_unsat(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    seeds: &[(ConceptId, bool)],
) -> Option<bool> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();
    algo.completeness_poisoned = false;

    // fresh root node (the classify_test `make_root`)
    let id = *next_indi_id;
    *next_indi_id += 1;
    let mut root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(id);
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(id, root);

    // Probe seeds are BASE assertions — track them on the independent base
    // dependency (a NONE would read as an unported rule path downstream).
    let seed_tp = ctx.get_or_create_base_dependency_track_point();
    // KONCLUDE-PORT-NOTE[root-top]: see `bridged_classify_subject` — every node
    // carries ⊤ in Konclude; a bare root swallowed derived ⊥ (¬⊤ met no ⊤).
    let top = ctx.processing_data_box().ontology_top_concept;
    if top.is_some() && std::env::var_os("KM_HT_NO_ROOT_TOP").is_none() {
        algo.add_concept_to_individual(top, false, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            return Some(true);
        }
    }
    let mut seed_start = 0usize;
    if algo.conf_expand_created_successors_from_saturation {
        if let Some(&(concept, negated)) = seeds.first() {
            if algo.try_initializing_concept_from_saturated_data(
                &mut root, concept, negated, seed_tp, true, ctx,
            ) {
                seed_start = 1;
                if ctx.has_pending_signal() {
                    return Some(true);
                }
            }
        }
    }
    for &(concept, negated) in &seeds[seed_start..] {
        algo.add_concept_to_individual(concept, negated, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                eprintln!("UNSAT-EXIT seed-insert");
            }
            return Some(true);
        }
    }

    // GLOBAL fixpoint on total insertions (see `bridged_classify_subject`):
    // root-label-count-stable is order-dependent and declared a false fixpoint.
    let trace = std::env::var_os("KM_BRIDGE_TRACE").is_some();
    // KM_BRIDGE_PROBE_BUDGET_S: wall-clock budget per probe. On overrun the
    // probe returns None (STOP — an UNKNOWN verdict the caller must treat as
    // a DEFER). A single pathological probe must never wedge a classify run.
    // `algo.probe_budget` (set by `bridged_classify`'s retry rounds) takes
    // precedence over the env so escalation needs no env mutation.
    let budget: Option<std::time::Duration> = algo.probe_budget.or_else(|| {
        std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .map(std::time::Duration::from_secs)
    });
    let probe_t0 = std::time::Instant::now();
    // Thread the deadline INTO the drive loop: one `run_completion_on` call
    // owns the whole backtracking search, so the between-passes check below
    // cannot bound it on its own.
    algo.drive_deadline = budget.map(|b| probe_t0 + b);
    let mut prev_inserts: i64 = -1;
    for pass in 0..256 {
        if let Some(b) = budget {
            if probe_t0.elapsed() > b {
                return None;
            }
        }
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        // Plain-mode completeness repair: reprocess every label concept each
        // pass, so the insertion-stable break below certifies genuine closure
        // under ALL rules (see `requeue_all_node_labels`).
        algo.requeue_all_node_labels(ctx);
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let backtracks_before = algo.or_backtrack_count;
        let consistent = algo.run_completion_on(ctx);
        if trace {
            eprintln!(
                "TRACE pass={pass} consistent={consistent} inserts={} backtracks={} nodes={}",
                algo.stat_con_des_insertion_count,
                algo.or_backtrack_count,
                ctx.process_context().node_count(),
            );
        }
        if !consistent {
            // A Clash is a genuine UNSAT; a Stop (iteration cap / task fork)
            // is an UNKNOWN — folding it into unsat would be UNSOUND, folding
            // it into sat would be INCOMPLETE.
            if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                eprintln!(
                    "UNSAT-EXIT pass={pass} signal={:?}",
                    matches!(
                        ctx.pending_signal(),
                        super::completion::clash::CalcSignal::Clash(_)
                    )
                );
            }
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(clash) => {
                    if std::env::var_os("KM_BRIDGE_TRACE2").is_some() {
                        eprintln!(
                            "UNSAT-EXIT probe-clash: ddb={} cow={} root_cancelled={} backtracks={} dumps_used={}",
                            algo.conf_dependency_backjumping,
                            algo.conf_inprocess_cow,
                            algo.ddb_root_cancelled,
                            algo.or_backtrack_count,
                            algo.ddb_analysis_dumps
                        );
                    }
                    if trace {
                        // walk the clash descriptor chain: which concepts on
                        // which nodes clashed (diff a clash run vs a SAT run).
                        let mut c = clash;
                        while c.is_some() {
                            let d = ctx.process_context().clash_desc(c);
                            let next = d.next;
                            if let super::process::descriptor::ClashDescriptorKind::Concept {
                                concept_descriptor,
                                individual_node,
                            } = &d.kind
                            {
                                let concept_descriptor = *concept_descriptor;
                                let individual_node = *individual_node;
                                let (tag, neg, node_id) = {
                                    let pc = ctx.process_context();
                                    let con = if concept_descriptor.is_some() {
                                        pc.con_desc(concept_descriptor).get_concept()
                                    } else {
                                        Id::NONE
                                    };
                                    (
                                        if con.is_some() {
                                            ctx.ontology_arenas().concept(con).get_concept_tag()
                                        } else {
                                            -1
                                        },
                                        concept_descriptor.is_some()
                                            && pc.con_desc(concept_descriptor).is_negated(),
                                        if individual_node.is_some() {
                                            pc.node(individual_node).individual_node_id()
                                        } else {
                                            -1
                                        },
                                    )
                                };
                                eprintln!("TRACE CLASH concept tag={tag} neg={neg} node={node_id}");
                                // full label of the clash node: which class was
                                // wrongly pushed is usually visible here (its
                                // disjointness supplies the negation).
                                if individual_node.is_some() {
                                    let ls = ctx
                                        .process_context_mut()
                                        .node_reapply_concept_label_set(individual_node);
                                    let mut parts: Vec<String> = ctx
                                        .process_context()
                                        .label_set(ls)
                                        .concept_des_dep_map
                                        .iter()
                                        .map(|(t, data)| {
                                            let n = if data.concept_descriptor.is_some()
                                                && ctx
                                                    .process_context()
                                                    .con_desc(data.concept_descriptor)
                                                    .is_negated()
                                            {
                                                "¬"
                                            } else {
                                                ""
                                            };
                                            format!("{n}{t}")
                                        })
                                        .collect();
                                    parts.sort();
                                    eprintln!("TRACE CLASH-NODE-LABEL {}", parts.join(" "));
                                }
                            } else {
                                use super::process::descriptor::ClashDescriptorKind as K;
                                match &d.kind {
                                    K::Dependency => eprintln!("TRACE CLASH dependency"),
                                    K::IndividualLink { link_edge } => {
                                        let pc = ctx.process_context();
                                        let (s, t, r) = if link_edge.is_some() {
                                            let e = pc.edge(*link_edge);
                                            (
                                                pc.node(e.get_source_individual())
                                                    .individual_node_id(),
                                                pc.node(e.get_destination_individual())
                                                    .individual_node_id(),
                                                e.get_link_role().index() as i64,
                                            )
                                        } else {
                                            (-1, -1, -1)
                                        };
                                        eprintln!("TRACE CLASH link {s}--role{r}-->{t}");
                                    }
                                    K::IndividualDistinct { distinct_edge } => {
                                        let pc = ctx.process_context();
                                        let (s, t) = if distinct_edge.is_some() {
                                            let e = pc.distinct_edge(*distinct_edge);
                                            (
                                                pc.node(e.source).individual_node_id(),
                                                pc.node(e.destination).individual_node_id(),
                                            )
                                        } else {
                                            (-1, -1)
                                        };
                                        eprintln!("TRACE CLASH distinct {s} != {t}");
                                    }
                                    _ => eprintln!("TRACE CLASH other-kind"),
                                }
                            }
                            c = next;
                        }
                    }
                    Some(true)
                }
                _ => None,
            };
        }
        let inserts = algo.stat_con_des_insertion_count;
        if inserts == prev_inserts && algo.or_backtrack_count == backtracks_before {
            break;
        }
        prev_inserts = inserts;
    }
    if trace {
        // Dump the final root label (sorted tags) so a SAT run can be diffed
        // against a clash run of the same probe.
        let ls = ctx
            .process_context_mut()
            .node_reapply_concept_label_set(root);
        let mut tags: Vec<(Cint64, bool)> = ctx
            .process_context()
            .label_set(ls)
            .concept_des_dep_map
            .iter()
            .filter_map(|(tag, data)| {
                let cd = data.concept_descriptor;
                if cd.is_none() {
                    return None;
                }
                Some((*tag, ctx.process_context().con_desc(cd).is_negated()))
            })
            .collect();
        tags.sort_unstable();
        eprintln!("TRACE root-label {tags:?}");

        // BLOCKING INVARIANT: at a claimed fixpoint every DIRECTBLOCKED node's
        // label must still be a SUBSET of its blocker's label (subset blocking).
        // A violation = the retest-on-modification chain failed for that node —
        // the order-dependent false-model mechanism.
        // Walk CURRENT nodes via the id→node vector (raw arena slots include
        // stale pre-localization copies whose old flags would false-positive).
        let max_id = ctx
            .processing_data_box()
            .individual_process_node_vector()
            .get_item_max_index();
        let mut blocked_count = 0usize;
        for indi_id in 0..=max_id.max(-1) {
            let nid = ctx
                .processing_data_box()
                .individual_process_node_vector()
                .get_data(indi_id);
            if nid.is_none() {
                continue;
            }
            let nid_idx = nid.index();
            let node = ctx.process_context().node(nid);
            if !node
                .has_partial_processing_restriction_flags(IndividualProcessNode::PRF_DIRECTBLOCKED)
            {
                continue;
            }
            blocked_count += 1;
            let blocker_raw = node.blocker_individual_node();
            let bls = node.use_reapply_con_label_set;
            if blocker_raw.is_none() || bls.is_none() {
                eprintln!("TRACE BLOCKVIOLATION node={nid_idx} blocker=NONE");
                continue;
            }
            // map the (possibly stale pre-localization) blocker NodeId to the
            // CURRENT node for its individual id.
            let blocker = {
                let blocker_id = ctx.process_context().node(blocker_raw).individual_node_id();
                let cur = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(blocker_id);
                if cur.is_some() {
                    cur
                } else {
                    blocker_raw
                }
            };
            let blocker_ls = ctx
                .process_context()
                .node(blocker)
                .use_reapply_con_label_set;
            if blocker_ls.is_none() {
                eprintln!("TRACE BLOCKVIOLATION node={nid_idx} blocker-label=NONE");
                continue;
            }
            let pc = ctx.process_context();
            let mut missing: Vec<(Cint64, bool)> = Vec::new();
            for (tag, data) in pc.label_set(bls).concept_des_dep_map.iter() {
                let cd = data.concept_descriptor;
                if cd.is_none() {
                    continue;
                }
                let neg = pc.con_desc(cd).is_negated();
                // by-tag probe (the map IS keyed by real concept tags) + explicit
                // polarity compare — ls1::has_concept is a W2-DEFER stub (raw-index
                // key + always-false negation) and must not be used here.
                let present = pc
                    .label_set(blocker_ls)
                    .concept_des_dep_map
                    .get(tag)
                    .map_or(false, |d| {
                        d.concept_descriptor.is_some()
                            && pc.con_desc(d.concept_descriptor).is_negated() == neg
                    });
                if !present {
                    missing.push((*tag, neg));
                }
            }
            if !missing.is_empty() {
                missing.sort_unstable();
                eprintln!(
                    "TRACE BLOCKVIOLATION node={nid_idx} blocker={} missing={missing:?}",
                    blocker.index()
                );
            }
        }
        eprintln!("TRACE blocked-nodes={blocked_count}");

        // KM_BRIDGE_DUMP_EDGES=<indi>[,<indi>...]: dump the outgoing edges of
        // the listed CURRENT nodes (role tag, destination id, ghost status).
        if let Some(spec) = std::env::var_os("KM_BRIDGE_DUMP_EDGES") {
            let ids: Vec<Cint64> = spec
                .to_string_lossy()
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for indi_id in ids {
                let nid = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(indi_id);
                if nid.is_none() {
                    eprintln!("TRACE EDGES indi={indi_id} <no node>");
                    continue;
                }
                let pc = ctx.process_context();
                let mut it = pc.node_successor_iterator(nid);
                while it.has_next() {
                    let link = it.next_link(false);
                    let succ_id = it.next_individual_id(true);
                    if link.is_none() {
                        continue;
                    }
                    let role_tag = {
                        let r = pc.edge(link).get_link_role();
                        if r.is_some() {
                            ctx.ontology_arenas().role(r).get_role_tag()
                        } else {
                            -1
                        }
                    };
                    let succ = ctx
                        .processing_data_box()
                        .individual_process_node_vector()
                        .get_data(succ_id);
                    let ghost = succ.is_some() && {
                        let n = pc.node(succ);
                        n.has_merged_into_individual_node_id()
                            || n.has_purged_blocked_processing_restriction_flags()
                    };
                    eprintln!(
                        "TRACE EDGES indi={indi_id} --role{role_tag}--> {succ_id} ghost={ghost}"
                    );
                }
            }
        }

        // KM_BRIDGE_FIND_TAG=<tag>[,<tag>...]: list every current node whose
        // label carries the tag (either polarity) + its blocking flags — used
        // to locate the clash region of a TRUE run inside a FALSE run's model.
        if let Some(spec) = std::env::var_os("KM_BRIDGE_FIND_TAG") {
            let tags: Vec<Cint64> = spec
                .to_string_lossy()
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for indi_id in 0..=max_id.max(-1) {
                let nid = ctx
                    .processing_data_box()
                    .individual_process_node_vector()
                    .get_data(indi_id);
                if nid.is_none() {
                    continue;
                }
                let pc = ctx.process_context();
                let node = pc.node(nid);
                let ls = node.use_reapply_con_label_set;
                if ls.is_none() {
                    continue;
                }
                for &t in &tags {
                    if let Some(d) = pc.label_set(ls).concept_des_dep_map.get(&t) {
                        if d.concept_descriptor.is_some() {
                            let neg = pc.con_desc(d.concept_descriptor).is_negated();
                            let flags = node.processing_restriction_flags();
                            let blocked = node.has_partial_processing_restriction_flags(
                                IndividualProcessNode::PRF_DIRECTBLOCKED
                                    | IndividualProcessNode::PRF_INDIRECTBLOCKED
                                    | IndividualProcessNode::PRF_PROCESSINGBLOCKED,
                            );
                            eprintln!(
                                "TRACE FINDTAG tag={t} neg={neg} indi={indi_id} blocked={blocked} flags={flags:#x} label-size={}",
                                pc.label_set(ls).get_concept_count()
                            );
                        }
                    }
                }
            }
        }
    }
    // A clash-free fixpoint after a cross-branch WIPE (see
    // `completeness_poisoned`) is not a model certificate — the graph may be
    // missing branch-independent consequences whose clash would have proved
    // UNSAT. Answer UNKNOWN (defer); clash exits above remain sound.
    if algo.completeness_poisoned {
        return None;
    }
    // Konclude calls `cacheSatisfiableIndividualNodes` at every successful
    // task fixpoint; that routine itself enters when either the signature
    // satisfiable-expander writer or the saturation-node writer is active.
    // The bridge drives completion directly, so it must reproduce the same OR
    // gate before committing both handlers' pending messages.
    if algo.conf_sat_exp_cache_writing
        || algo.conf_saturation_satisfiabilitiy_expansion_cache_writing
    {
        let wrote = algo.cache_satisfiable_individual_nodes(ctx);
        algo.commit_cache_messages(ctx);
        if wrote && std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
            eprintln!("BRIDGE-SAT-EXPANSION-CACHE-WRITE");
        }
    }
    Some(false)
}

/// Model READ-OFF classification of one named concept.
///
/// Saturates `{named[subject]}` on a fresh root and reads the root label's
/// positive NAMED tags as `subject`'s subsumers — O(1) saturation per
/// concept instead of O(concepts) pairwise probes. VALID only when the
/// saturation is deterministic (`or_backtrack_count` unchanged): one
/// canonical model then captures every consequence, so a named concept in
/// the label IS a subsumer (Horn/EL read-off). On a NON-deterministic
/// subject the single branch is not authoritative — the caller must fall
/// back to pairwise `bridged_unsat` probes over the candidate set.
///
/// Returns `Some((subsumer_indices, authoritative))` (indices into
/// `bridged.named`, INCLUDING `subject` itself), `None` if the drive
/// STOPped (no verdict at all). `authoritative = true` ⇔ the saturation made
/// NO nondeterministic choice (no OR branch point opened, no backtrack): the
/// canonical model captures every consequence and the read-off IS the
/// subsumer set. `authoritative = false` ⇔ the label is one branch's model —
/// the positives are CANDIDATE subsumers (Konclude's possible-subsumer
/// extraction) the caller must verify individually via `bridged_unsat`
/// pairwise probes. A clash means the subject is unsatisfiable — every
/// concept subsumes it — reported as the full index range, authoritative.
fn bridged_classify_subject_with_root(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    subject: usize,
    n_named: usize,
) -> Option<(Vec<usize>, bool, NodeId)> {
    ctx.clear_pending_signal();
    algo.or_branch_stack.clear();
    algo.completeness_poisoned = false;
    // KM_BRIDGE_PROBE_BUDGET_S also bounds the READ-OFF search: before the
    // DDB taint fix (2a869e8) heavy subjects' read-offs looked fast only
    // because wrong root-cancels cut them short; the genuine search is
    // unbounded without a deadline (measured: SUBJ PathOfLength3 read-off ran
    // 10 min to 126 GB). On overrun the drive raises a STOP → verdict None →
    // the caller records NO derivations for the subject (sound; shows as
    // missing vs gold, never spurious).
    algo.drive_deadline = algo
        .probe_budget
        .or_else(|| {
            std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
                .ok()
                .and_then(|s| s.parse::<u64>().ok())
                .map(std::time::Duration::from_secs)
        })
        .map(|b| std::time::Instant::now() + b);

    let id = *next_indi_id;
    *next_indi_id += 1;
    let mut root = ctx
        .process_context_mut()
        .alloc_node(IndividualProcessNode::new(Id::NONE));
    ctx.process_context_mut()
        .node_mut(root)
        .set_individual_node_id(id);
    ctx.processing_data_box_mut()
        .individual_process_node_vector_mut()
        .set_local_data(id, root);

    // The subject seed is a BASE assertion — independent base dependency.
    let seed_tp = ctx.get_or_create_base_dependency_track_point();
    // KONCLUDE-PORT-NOTE[root-top]: Konclude's node initialization labels EVERY
    // node with ⊤ (`create_new_individual` does it for successors); bridge roots
    // were created bare, so the bottom rule's faithful ¬⊤ insert (u08) met no ⊤
    // and a derived ⊥ on the ROOT was silently satisfiable — an under-detected
    // unsat (found by the saturation-first oracle tests: A ⊑ B, A ⊓ B ⊑ ⊥ was
    // classified SAT). Labeling the root with ⊤ arms the ⊤/¬⊤ clash pair and,
    // via the CCTOP AND-unfold, delivers the top-attached GCIs exactly like the
    // per-pass re-seed already did (idempotent).
    let top = ctx.processing_data_box().ontology_top_concept;
    if top.is_some() && std::env::var_os("KM_HT_NO_ROOT_TOP").is_none() {
        algo.add_concept_to_individual(top, false, &mut root, seed_tp, false, true, ctx);
        if ctx.has_pending_signal() {
            return Some(((0..n_named).collect(), true, root));
        }
    }
    let initialized_from_saturation = algo.conf_expand_created_successors_from_saturation
        && algo.try_initializing_concept_from_saturated_data(
            &mut root,
            bridged.named[subject],
            false,
            seed_tp,
            true,
            ctx,
        );
    if !initialized_from_saturation {
        algo.add_concept_to_individual(
            bridged.named[subject],
            false,
            &mut root,
            seed_tp,
            false,
            true,
            ctx,
        );
    }
    if ctx.has_pending_signal() {
        // seed alone clashed ⇒ subject unsatisfiable
        return Some(((0..n_named).collect(), true, root));
    }

    let backtracks_before = algo.or_backtrack_count;
    let branch_opens_before = algo.or_branch_open_count;
    // GLOBAL fixpoint: break only when a full re-drive pass inserts NO concept
    // on ANY node. Breaking on the root-label COUNT (the earlier criterion) is
    // order-dependent — a pass can add nothing to the root while reapply /
    // successor→root propagation is still pending, so it declared a fixpoint
    // at an INCOMPLETE, HashMap-order-dependent closure (identical runs gave
    // different subsumer sets). `stat_con_des_insertion_count` is the total
    // insertions across every node; unchanged over a pass ⇒ true fixpoint.
    let mut prev_inserts: i64 = -1;
    for _ in 0..256 {
        for &g in &bridged.tbox {
            seed_concept_on_queue(ctx, root, g);
        }
        // Plain-mode completeness repair: reprocess every label concept each
        // pass, so the insertion-stable break below certifies genuine closure
        // under ALL rules (see `requeue_all_node_labels`).
        if !bridged.source_tbox {
            algo.requeue_all_node_labels(ctx);
        }
        let iq = ctx.get_individual_immediately_processing_queue(true);
        ctx.process_context_mut()
            .indi_unsorted_proc_queue_mut(iq)
            .insert_indiviudal_process_node(root);
        let consistent = algo.run_completion_on(ctx);
        if !consistent {
            return match ctx.pending_signal() {
                super::completion::clash::CalcSignal::Clash(_) => {
                    Some(((0..n_named).collect(), true, root))
                }
                _ => None, // STOP: no verdict
            };
        }
        if bridged.source_tbox {
            break;
        }
        let inserts = algo.stat_con_des_insertion_count;
        if inserts == prev_inserts {
            break;
        }
        prev_inserts = inserts;
    }
    // A cross-branch WIPE (see `completeness_poisoned`) invalidates BOTH
    // read-off directions: the label may miss branch-independent positives
    // (candidate set no longer ⊇ true subsumers) AND absences are no longer
    // countermodels. No usable verdict — defer the subject.
    if algo.completeness_poisoned {
        return None;
    }
    if algo.conf_sat_exp_cache_writing
        || algo.conf_saturation_satisfiabilitiy_expansion_cache_writing
    {
        let wrote = algo.cache_satisfiable_individual_nodes(ctx);
        algo.commit_cache_messages(ctx);
        if wrote && std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
            eprintln!("BRIDGE-SAT-EXPANSION-CACHE-WRITE");
        }
    }
    // Non-deterministic saturation ⇒ single branch is not authoritative.
    // Opened branch points count even without backtracks: a drive committing
    // to first disjuncts pollutes the root label with branch-dependent
    // concepts (measured on ore_ont_3215: 86 SPURIOUS subsumptions under the
    // backtrack-only gate). The read-off still runs — its positives become
    // the CANDIDATE set for pairwise verification.
    let authoritative = algo.or_backtrack_count == backtracks_before
        && algo.or_branch_open_count == branch_opens_before;

    // Read off positive named tags from the root label.
    let ls = ctx
        .process_context_mut()
        .node_reapply_concept_label_set(root);
    let mut subsumers: Vec<usize> = Vec::new();
    let entries: Vec<(Cint64, super::process::ConDescId)> = ctx
        .process_context()
        .label_set(ls)
        .concept_des_dep_map
        .iter()
        .map(|(tag, data)| (*tag, data.concept_descriptor))
        .collect();
    for (tag, cd) in entries {
        if tag < TAG_BASE || tag >= TAG_BASE + n_named as Cint64 {
            continue;
        }
        if cd.is_none() {
            continue;
        }
        if ctx.process_context().con_desc(cd).is_negated() {
            continue;
        }
        subsumers.push((tag - TAG_BASE) as usize);
    }
    subsumers.sort_unstable();
    subsumers.dedup();
    Some((subsumers, authoritative, root))
}

pub fn bridged_classify_subject(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    next_indi_id: &mut i64,
    subject: usize,
    n_named: usize,
) -> Option<(Vec<usize>, bool)> {
    bridged_classify_subject_with_root(algo, ctx, bridged, next_indi_id, subject, n_named)
        .map(|(subsumers, authoritative, _)| (subsumers, authoritative))
}

/// Run Konclude's already-ported classification-message analyser over a
/// completed bridge model and feed the resulting subsumer, possible-subsumer,
/// and pseudo-model messages into the persistent KPSet item.
fn analyse_kpset_completion_model(
    classifier: &mut OptimizedKPSetClassSubsumptionClassifierThread,
    state: &mut SynchronousKPSetClassState,
    subject: usize,
    root: NodeId,
    ctx: &mut CalculationAlgorithmContextBase,
) {
    let analyser = SatisfiableTaskClassificationMessageAnalyser::default();
    let adapter = SatisfiableTaskClassificationMessageAdapter::new_with_handles(
        state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[subject].index()]
        .get_testing_concept(),
        0,
        0,
        state
            .ontology_item
            .get_concept_reference_linking_data_hash()
            .clone(),
        EFEXTRACTALL,
    );
    let individual_vector = ctx
        .processing_data_box()
        .individual_process_node_vector()
        .clone();
    let max_branch_tag = ctx.processing_data_box().maximum_deterministic_branch_tag();
    let mut observer = RecordingClassificationMessageDataObserver::new();
    let testing_items = state
        .ontology_item
        .get_concept_satisfiable_test_item_container();
    // `mEquivConNonCandidateSet` belongs to the live TBox in Konclude. Split
    // the two disjoint context fields so the analyser can update completion
    // bookkeeping while reading that ontology-owned set.
    let base = &mut ctx.base;
    let process_context = &mut base.used_process_context;
    let ontology = &base.ontology_arenas;
    let analysed = analyser.analyse_satisfiable_task_classification_messages_with_live_other_nodes_and_live_equivalent_non_candidates(
        &adapter,
        process_context,
        ontology,
        root,
        &individual_vector,
        max_branch_tag,
        ontology.concepts(),
        ontology.concept_process_datas(),
        ontology.concept_saturation_reference_linking_datas(),
        ontology.saturation_concept_reference_linkings(),
        testing_items,
        ontology.roles(),
        false,
        0,
        Some(&mut observer),
    );
    let Some(analysed) = analysed else { return };
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        let message_count: usize = observer
            .get_told_messages()
            .iter()
            .map(|(_, messages, _)| messages.len())
            .sum();
        eprintln!(
            "BRIDGE-KPSET-MESSAGES subject {subject}: visits={} messages={message_count}",
            analysed.other_node_visit_count,
        );
    }
    for (_, messages, _) in observer.get_told_messages() {
        classifier.process_classification_message_data_linker(
            &mut state.ontology_item,
            messages,
            ontology.concepts(),
        );
    }
}

/// The production classification result: index pairs into `TInput.concepts`.
pub struct BridgedClassification {
    /// Indices of unsatisfiable named concepts.
    pub unsatisfiable: Vec<usize>,
    /// `(sub, sup)` subsumption pairs (self-pairs excluded).
    pub subsumptions: Vec<(usize, usize)>,
}

/// Fresh per-subject probe environment: algorithm + context + bridged
/// terminology. Konclude isolates probes via per-task databox COW (the
/// unported Task layer); the v1 driver rebuilds — same verdicts, O(TBox)
/// per subject/probe.
/// Install a live `CUnsatisfiableCacheHandler` (occurrence unsat cache +
/// reader/writer) into the probe context — the store `KM_HT_UNSATCACHE`'s
/// write/read paths use. One cache per bridge env; `reset_probe_env` carries
/// it across probe resets so nogoods learned in probe k prune probe k+1
/// (Konclude shares the cache across ALL tests of an ontology).
fn install_bridge_unsat_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::cache::context::CacheContext;
    use super::cache::unsat::OccurrenceUnsatisfiableCache;
    use super::completion::unsat_handler::UnsatisfiableCacheHandler;
    let mut cache_context = CacheContext::new();
    // KONCLUDE-PORT-NOTE[slots]: Konclude sizes the write-slot ring as
    // `workControllerCount + 2` (CExperimentalReasonerManager cpp 58). With
    // ONE slot the ring deadlocks after the first write: the activation pins
    // the slot through the reader's next-pointer, and the release needs a
    // SECOND slot to displace it — `wait_cache_write_prepared` then spins
    // forever (measured: the tiny warm-probes test hung at 100% CPU). The
    // bridge is single-threaded ⇒ 1 worker + 2 = 3.
    let cache = cache_context.alloc_unsat_cache(OccurrenceUnsatisfiableCache::new(3, "", 0));
    {
        let CacheContext {
            unsat_caches,
            unsat_cache_entries,
            unsat_cache_update_slot_items,
            ..
        } = &mut cache_context;
        unsat_caches
            .get_mut(cache)
            .thread_started(unsat_cache_entries, unsat_cache_update_slot_items);
    }
    let reader = {
        let CacheContext {
            unsat_caches,
            unsat_cache_readers,
            ..
        } = &mut cache_context;
        unsat_caches
            .get_mut(cache)
            .get_cache_reader(cache, unsat_cache_readers)
    };
    let writer = {
        let CacheContext {
            unsat_caches,
            unsat_cache_writers,
            ..
        } = &mut cache_context;
        unsat_caches
            .get_mut(cache)
            .get_cache_writer(cache, unsat_cache_writers)
    };
    ctx.base.install_used_unsatisfiable_cache_handler(
        UnsatisfiableCacheHandler::new(reader, writer),
        cache_context,
    );
}

/// Install Konclude's ontology-wide saturation-node associated-expansion
/// cache. Successful classification jobs extend this cache; later roots and
/// successors replay its deterministic expansions before tableau search.
fn install_bridge_saturation_node_expansion_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::cache::context::CacheContext;
    use super::cache::satnode::{
        SaturationNodeAssociatedExpansionCache, SaturationNodeAssociatedExpansionCacheWriter,
    };
    use super::completion::sat_node_exp_handler::SaturationNodeExpansionCacheHandler;
    use super::model::substrate::Id;

    let mut cache_context = CacheContext::new();
    let cache =
        cache_context.alloc_sat_expansion_cache(SaturationNodeAssociatedExpansionCache::new());
    let writer = SaturationNodeAssociatedExpansionCacheWriter::new(cache);
    let handler = SaturationNodeExpansionCacheHandler::new(Id::NONE, writer);
    ctx.install_used_saturation_node_expansion_cache_handler(handler, cache_context);
}

/// Install Konclude's ontology-wide signature satisfiable-expander cache. Its
/// reader/writer state is shared by every classification job and survives the
/// bridge's per-probe databox reset, exactly like the reasoner-manager cache in
/// Konclude.
fn install_bridge_satisfiable_expander_cache(ctx: &mut CalculationAlgorithmContextBase) {
    use super::completion::stubs::SatisfiableExpanderCacheHandler;
    ctx.install_used_satisfiable_expander_cache_handler(SatisfiableExpanderCacheHandler::new());
}

fn log_bridge_satisfiable_expander_cache_stats(
    ctx: &CalculationAlgorithmContextBase,
    phase: &str,
    subject: usize,
) {
    if std::env::var_os("KM_HT_SATEXP_STATS").is_none() {
        return;
    }
    if let Some(state) = ctx.base.used_sat_exp_cache_handler_state.as_ref() {
        let handler = &state.handler;
        let mut direct_cached = 0usize;
        let mut ancestor_cached = 0usize;
        for index in 0..ctx.process_context().node_count() {
            let node = ctx.process_context().node(NodeId::new(index as Cint64));
            direct_cached += usize::from(node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_SATISFIABLECACHED,
            ));
            ancestor_cached += usize::from(node.has_partial_processing_restriction_flags(
                IndividualProcessNode::PRF_ANCESTORSATISFIABLECACHED,
            ));
        }
        eprintln!(
            "SATEXP-STATS phase={phase} subject={subject} entries={} read={}/{}/{} sat={} sat-compat={}/{}/{} cached-nodes={}/{} write-requests={}/{} writes={}/{} commits={}",
            handler.cache.sig_item_hash.len(),
            handler.stat_retrieval_requests,
            handler.stat_signature_hits,
            handler.stat_compatible_hits,
            handler.stat_satisfiable_hits,
            handler.stat_satisfiable_compatibility_tests,
            handler.stat_compatible_satisfiable_hits,
            handler.stat_incompatible_satisfiable_hits,
            direct_cached,
            ancestor_cached,
            handler.stat_expansion_write_requests,
            handler.stat_satisfiable_write_requests,
            handler.stat_expansion_writes,
            handler.stat_satisfiable_writes,
            handler.stat_commit_batches,
        );
    }
}

fn fresh_bridge_env(
    tin: &TInput,
) -> (
    CompletionTaskHandleAlgorithm,
    CalculationAlgorithmContextBase,
    Bridged,
) {
    use super::completion::strategy::ConceptProcessingPriorityStrategy;
    let mut algo = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut algo);
    let mut ctx = CalculationAlgorithmContextBase::new();
    ctx.base.used_concept_priority_strategy =
        Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
    if std::env::var_os("KM_HT_UNSATCACHE").is_some() {
        install_bridge_unsat_cache(&mut ctx);
    }
    let top = {
        let mut c = Concept::new();
        c.set_concept_tag(1);
        c.set_operator_code(op::CCTOP);
        ctx.ontology_arenas_mut().alloc_concept(c)
    };
    ctx.processing_data_box_mut().ontology_top_concept = top;
    let bridged = bridge_tinput(&mut ctx, tin);
    algo.singleton_concepts = bridged.singleton_concepts.clone();
    (algo, ctx, bridged)
}

/// Reset the probe environment to its post-`bridge_tinput` pristine state
/// WITHOUT rebuilding the bridged terminology. Sound because the ontology
/// arenas are READ-ONLY during bridge probes: the only drive paths that
/// mutate them (nominal grounding, temporary nominal individuals) are gated
/// out of the bridge fragment (`tin.nominals.is_empty()`), so keeping the
/// arenas and replacing every piece of per-probe state reproduces
/// `fresh_bridge_env`'s output exactly — the arena content is a
/// deterministic function of `tin` alone. This is the v2 stand-in for
/// Konclude's per-task databox COW: O(processing state) per probe instead
/// of O(TBox) (measured ~seconds + hundreds of MB per probe on the 3215
/// family).
fn reset_probe_env(
    algo: &mut CompletionTaskHandleAlgorithm,
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
    preserve_saturation: bool,
) {
    use super::model::ontology::OntologyArenas;
    // Fresh algorithm: search state (OR stack, DDB marks, blocking caches,
    // stats, deadlines) must not leak between probes. Same construction as
    // `fresh_bridge_env` so verdicts are identical.
    let budget = algo.probe_budget;
    let mut a = CompletionTaskHandleAlgorithm::new();
    configure_default_blocking(&mut a);
    a.singleton_concepts = bridged.singleton_concepts.clone();
    a.probe_budget = budget;
    *algo = a;
    // Fresh context EXCEPT the shared read-only terminology: rebuild through
    // the same ctor as `fresh_bridge_env`, then graft the arenas back. This
    // resets EVERY per-probe field (process context, databox, dependency
    // factory ids, epoch stack, pending signal) by construction rather than
    // by enumeration.
    let arenas = std::mem::replace(&mut ctx.base.ontology_arenas, OntologyArenas::new());
    let strategy = ctx.base.used_concept_priority_strategy.take();
    let top = ctx.base.used_processing_data_box.ontology_top_concept;
    // KM_HT_UNSATCACHE: the learned-nogood store DELIBERATELY survives the
    // probe reset (Konclude shares its unsatisfiable cache across all tests
    // of an ontology). Sound: each entry is a label subset validated by the
    // u22 write guards to be unsatisfiable wrt the shared TBox alone, so it
    // prunes any later probe identically. Note the cache write path also
    // stamps caching tags into the ontology arenas' concept process data — a
    // monotone cache-metadata mutation; with the flag OFF the arenas stay
    // read-only and the reset reproduces `fresh_bridge_env` exactly, with it
    // ON later probes are deliberately order-dependent (they prune using
    // earlier probes' nogoods) while verdicts stay sound+complete.
    let unsat_cache = ctx.base.take_used_unsatisfiable_cache_handler();
    let satisfiable_expander_cache = ctx.take_used_satisfiable_expander_cache_handler();
    let sat_node_expansion_cache = ctx.take_used_saturation_node_expansion_cache_handler();
    // KM_HT_SATURATION: the saturation-side arenas DELIBERATELY survive the
    // probe reset when a saturation pass ran on this env — the ontology
    // arenas (kept above) hold concept→saturation reference linkings whose
    // node ids point into these arenas, and the saturation-node coupling
    // (u08/u17/u22, Konclude's expand-from-saturation + caching-blocking)
    // reads them during every probe. Probes never write them, so the carry
    // reproduces Konclude's stable saturation-task pointers. Carried even
    // when the coupling is off (budget-aborted pass) so the linkings never
    // dangle.
    let mut fresh = CalculationAlgorithmContextBase::new();
    if preserve_saturation {
        fresh
            .process_context_mut()
            .adopt_saturation_state_from(ctx.process_context_mut());
    }
    *ctx = fresh;
    ctx.base.ontology_arenas = arenas;
    ctx.base.used_concept_priority_strategy = strategy;
    ctx.base.used_processing_data_box.ontology_top_concept = top;
    if let Some(state) = unsat_cache {
        ctx.base.restore_used_unsatisfiable_cache_handler(state);
    }
    if let Some(state) = satisfiable_expander_cache {
        ctx.restore_used_satisfiable_expander_cache_handler(state);
    }
    if let Some(state) = sat_node_expansion_cache {
        ctx.restore_used_saturation_node_expansion_cache_handler(state);
    }
}

/// Production search configuration for `bridged_classify`. KPSet's message
/// analyser distinguishes deterministic subsumers and pseudo-model entries by
/// dependency branch tag, so classifier jobs must build the dependency spine
/// even when dependency-directed backjumping itself remains opt-in.
fn configure_production_search(algo: &mut CompletionTaskHandleAlgorithm) {
    algo.conf_build_dependencies = true;
}

/// Konclude's completion-side coupling to the precomputed saturation graph.
/// These are the flags used by classification jobs after saturation data has
/// been installed. In particular, cache reading is required to revalidate a
/// saturation-cached node after direct modification; without it the retest
/// path drops successor-creation blocking and expands the cached subtree.
fn configure_production_completion_saturation_coupling(algo: &mut CompletionTaskHandleAlgorithm) {
    // The `KM_HT_NO_*` switches are diagnostic cuts through Konclude's
    // completion-side saturation coupling. They leave production unchanged
    // unless explicitly set and let ontology traces isolate the first
    // divergent half without disabling the saturation pre-pass itself.
    algo.conf_expand_created_successors_from_saturation =
        std::env::var_os("KM_HT_NO_SAT_SUCCESSOR_EXPANSION").is_none();
    algo.conf_caching_blocking_from_saturation =
        std::env::var_os("KM_HT_NO_SAT_CACHING_BLOCKING").is_none();
    // CCalculationTableauCompletionTaskHandleAlgorithm.cpp ctor lines
    // 226-229 deliberately leave this OFF: the dependency for a resolved
    // successor must include the resolved universal restrictions, which that
    // path does not yet construct.  Do not enable the otherwise ported u22
    // resolver in production completion until Konclude does.
    algo.conf_successor_saturation_expansion_restrictions_resolving = false;
    // CCalculationTableauCompletionTaskHandleAlgorithm ctor lines 188-190.
    // These three absorption switches are independent of cache establishment:
    // they park rules while the corresponding cache flag remains valid and the
    // u10/u21 reapply paths restore them if that flag is later abolished.
    let cached_absorption = std::env::var_os("KM_HT_NO_SAT_CACHED_ABSORPTION").is_none();
    algo.conf_sat_exp_cached_disj_absorp = cached_absorption;
    algo.conf_sat_exp_cached_merg_absorp = cached_absorption;
    algo.conf_sat_exp_cached_succ_absorp = cached_absorption;
    // CCalculationTableauCompletionTaskHandleAlgorithm.cpp ctor line 237.
    algo.conf_saturation_expansion_cache_reading =
        std::env::var_os("KM_HT_NO_SAT_CACHE_READING").is_none();
}

// ---------------------------------------------------------------------------
// Saturation-first probe answering (task #23).
//
// Konclude decides ~95% of its classification work by the cheap non-branching
// approximation saturation and runs the backtracking tableau only on the
// residue (docs/KONCLUDE-STUDY.md). This section wires the ported saturation
// units (saturation/s01..s12) in front of the bridge's completion probes:
// saturate ONCE per classification in a dedicated env, extract per-named
// verdicts + certain subsumers, and let `bridged_classify` answer whole
// subjects from them — every UNKNOWN falls through to the existing probe path
// unchanged. Opt-in via KM_HT_SATURATION=1 (how to run it in production is a
// separate decision; nothing in the default path changes).
// ---------------------------------------------------------------------------

/// Konclude's PRODUCTION saturation configuration: `readCalculationConfig`
/// (CCalculationTableauApproximationSaturationTaskHandleAlgorithm cpp 180–237,
/// config-present branch, non-EL structure path) with the config defaults from
/// CReasonerConfigurationGroup.cpp 440–451 (SaturationCriticalConceptTesting =
/// true, SaturationDirectCriticalToInsufficient = false,
/// SaturationSuccessorExtension = true) plus the ctor defaults (cpp 130–170)
/// for the fields readCalculationConfig leaves untouched.
fn configure_production_saturation(
    algo: &mut super::saturation::algorithm::SaturationTaskHandleAlgorithm,
) {
    algo.conf_force_all_concept_insertion = true; // cpp 191 (non-EL / ABox path)
    algo.conf_implication_adding_skipping = false; // cpp 192
    algo.conf_force_all_copy_instead_of_substituition = false; // cpp 185
    algo.conf_directly_critical_to_insufficient = false; // cfg 444 default false
    algo.conf_add_critical_concepts_to_queues = true; // cfg 440 default true
    algo.conf_check_critical_concepts = true; // cfg 440 default true

    // CReasonerConfigurationGroup.cpp 448 installs `true`; the reader's local
    // fallback `false` applies only when the property is absent from the
    // configuration group. This is the configuration used by Konclude's
    // production precomputation.
    let sat_ext = std::env::var_os("KM_HT_NO_SAT_SUCCESSOR_EXTENSION").is_none();
    algo.conf_concepts_extension_processing = sat_ext;
    algo.conf_all_concepts_extension_processing =
        sat_ext && std::env::var_os("KM_HT_NO_SAT_ALL_EXTENSION").is_none();
    algo.conf_functional_concepts_extension_processing =
        sat_ext && std::env::var_os("KM_HT_NO_SAT_FUNCTIONAL_EXTENSION").is_none();
    algo.conf_nominal_processing = true; // cfg 497 (inert: nominal-free fragment)
                                         // ctor defaults (cpp 152–168):
    algo.conf_copy_node_from_top_individual_for_many_concepts = true;
    algo.conf_detailed_merging_test_for_atmost_critical_testing = true;
    algo.conf_simple_merging_test_for_atmost_critical_testing = true;
    algo.conf_delayed_merging_critical_atmost_concepts = true;
    algo.conf_delayed_merging_critical_atmost_concepts_cardinality_size = 100;
    algo.conf_resolve_operand_concept_size = 100;
    algo.conf_referred_node_many_concept_count = 500;
    algo.conf_many_concept_referred_node_count_process_limit = 2;
    algo.conf_referred_node_concept_count_process_limit = 1500;
    algo.conf_referred_node_unprocessed_count_process_limit = 1;
    algo.conf_referred_node_checking_depth = 5;
}

/// Port of `CExtractPropagationIntoCreationDirectionPreProcess::preprocess`
/// (Reasoner/Preprocess, cpp 39–105) over the bridged arenas: mark every
/// ∀/∃-family concept whose role can also appear in successor-CREATION
/// direction — the saturation ALL rule keys its criticality escape hatch on
/// this flag (without it a `∃R.C ⊓ ∀R.¬C` node would complete SAT-certain).
///
/// KONCLUDE-PORT-NOTE[identity]: `creationRoleHash` is filled from the
/// creation role's indirect super-role list, which in Konclude STARTS with the
/// role itself; the bridge builds strict lists, so the role is inserted
/// explicitly (see `saturation_indirect_super_roles`).
/// KONCLUDE-PORT-NOTE[api]: the C++ also stamps
/// `CRoleProcessData::setPropagationAndCreationConceptsFlag` — CRoleProcessData
/// is unported; the single consumer (applyALLRule's else arm) treats absent
/// role data exactly as flag-set (see the s04 port note).
fn extract_propagation_into_creation_direction(ctx: &mut CalculationAlgorithmContextBase) {
    use super::model::concept_process::ConceptProcessData;
    use super::model::op::{CCFS_ALL_AQALL_TYPE, CCFS_POSSIBLE_ROLE_CREATION_TYPE};
    let n = ctx.ontology_arenas().concept_count();
    let mut creation_roles: std::collections::HashSet<RoleId> = std::collections::HashSet::new();
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (is_creation, role) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_concept_operator()
                    .has_partial_operator_code_flag(CCFS_POSSIBLE_ROLE_CREATION_TYPE),
                c.get_role(),
            )
        };
        if is_creation && role.is_some() && !creation_roles.contains(&role) {
            creation_roles.insert(role); // [identity]
            let supers: Vec<super::model::substrate::NegLink<RoleId>> = ctx
                .ontology_arenas()
                .role(role)
                .get_indirect_super_role_list()
                .to_vec();
            for s in supers {
                if !s.negated {
                    creation_roles.insert(s.target);
                }
            }
        }
    }
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (flagged, role, concept_data) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_concept_operator().has_partial_operator_code_flag(
                    CCFS_ALL_AQALL_TYPE | CCFS_POSSIBLE_ROLE_CREATION_TYPE,
                ),
                c.get_role(),
                c.get_concept_data(),
            )
        };
        if flagged && role.is_some() && creation_roles.contains(&role) {
            let arenas = ctx.ontology_arenas_mut();
            let con_proc_data = if concept_data == super::model::substrate::INVALID {
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(cid).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            };
            arenas
                .concept_process_data_mut(con_proc_data)
                .propagation_into_creation_direction = true;
        }
    }
}

/// Port of the CONSTRUCTION half of
/// `CTotallyPrecomputationThread::createConceptSaturationProcessingJob`
/// (Reasoner/Consistiser cpp 2022–2230) +
/// `CSatisfiableCalculationTaskFromCalculationJobGenerator::createApproximatedSaturationCalculationTask`
/// (Reasoner/Generator cpp 40–163): one saturation seed per (concept, polarity)
/// item, plus Konclude's separate (role, concept, polarity) successor item
/// whenever the role has ranges. Each item gets a pre-built saturation node,
/// is registered in the databox node vector, and is queued for processing.
///
/// The leaf-first ordering, SUBSTITUTE/COPY assignment, and reachable
/// disjunct-candidate extension items are ported below. The role-range items
/// are essential after the bridge installs native CRole domain/range linkers:
/// their nodes initialize with `initRole`, exactly as Konclude requires.
fn build_saturation_seeds(ctx: &mut CalculationAlgorithmContextBase, bridged: &Bridged) {
    use super::model::concept_process::{
        ConceptProcessData, ConceptSaturationReferenceLinkingData,
        SaturationConceptReferenceLinking, SaturationConceptReferenceLinkingId,
        SATURATION_COPY_MODE, SATURATION_SUBSTITUTE_MODE,
    };
    use super::model::op::{
        CCALL, CCAND, CCAQAND, CCAQCHOOCE, CCAQSOME, CCATLEAST, CCATMOST, CCATOM, CCEQ, CCIMPLTRIG,
        CCOR, CCSOME, CCSUB,
    };
    use super::process::sat_linker::IndividualSaturationProcessNodeLinkerId;
    use super::process::sat_node::IndividualSaturationProcessNode;
    use super::process::sat_ref::ExtendedConceptReferenceLinkingData;

    #[derive(Clone, Copy)]
    struct Seed {
        concept: ConceptId,
        negated: bool,
        role_ranges: RoleId,
        potentially_exist: bool,
    }

    // Construction items, C++ 2022-2127. Only existential/cardinality fillers
    // are potentially-exist items; marking every seed disabled substitution.
    let mut seeds: Vec<Seed> = Vec::new();
    let mut seed_index: HashMap<(ConceptId, bool), usize> = HashMap::new();
    let mut role_seed_index: HashMap<(RoleId, ConceptId, bool), usize> = HashMap::new();
    let push = |seeds: &mut Vec<Seed>,
                seed_index: &mut HashMap<(ConceptId, bool), usize>,
                concept: ConceptId,
                negated: bool,
                potentially_exist: bool|
     -> usize {
        if concept.is_none() {
            return usize::MAX;
        }
        if let Some(&index) = seed_index.get(&(concept, negated)) {
            seeds[index].potentially_exist |= potentially_exist;
            index
        } else {
            let index = seeds.len();
            seeds.push(Seed {
                concept,
                negated,
                role_ranges: RoleId::NONE,
                potentially_exist,
            });
            seed_index.insert((concept, negated), index);
            index
        }
    };
    let push_role = |seeds: &mut Vec<Seed>,
                     role_seed_index: &mut HashMap<(RoleId, ConceptId, bool), usize>,
                     role: RoleId,
                     concept: ConceptId,
                     negated: bool,
                     potentially_exist: bool|
     -> usize {
        if concept.is_none() || role.is_none() {
            return usize::MAX;
        }
        if let Some(&index) = role_seed_index.get(&(role, concept, negated)) {
            seeds[index].potentially_exist |= potentially_exist;
            index
        } else {
            let index = seeds.len();
            seeds.push(Seed {
                concept,
                negated,
                role_ranges: role,
                potentially_exist,
            });
            role_seed_index.insert((role, concept, negated), index);
            index
        }
    };

    // Exact `hasRoleRanges`: inspect the range side of every signed indirect
    // super role. The local helper restores Konclude's reflexive role entry
    // for saturation without changing the completion arena's role lists.
    let roles_with_ranges: std::collections::HashSet<RoleId> = (0..ctx
        .ontology_arenas()
        .role_count())
        .map(RoleId::new)
        .filter(|&role| {
            super::saturation::algorithm::SaturationTaskHandleAlgorithm::saturation_indirect_super_roles(
                role,
                ctx,
            )
            .iter()
            .any(|super_link| {
                !ctx.ontology_arenas()
                    .role(super_link.target)
                    .get_domain_range_concept_list(!super_link.negated)
                    .is_empty()
            })
        })
        .collect();
    // Restriction concept -> its role-specific successor item. Konclude wires
    // this through mExistentialSuccessorSatConRefLinking (cpp 2071-2074).
    let mut existential_successor_seed: Vec<(ConceptId, usize)> = Vec::new();
    let top = ctx.processing_data_box().ontology_top_concept;
    push(&mut seeds, &mut seed_index, top, false, false);
    for &named in &bridged.named {
        // `createSaturationConstructionJob` seeds class-named concepts, not
        // every concept-vector entry. Q_/definer atoms deliberately have no
        // class-name linker in the bridge, just like Konclude's anonymous
        // structural concepts.
        if ctx.ontology_arenas().concept(named).has_class_name() {
            push(&mut seeds, &mut seed_index, named, false, false);
        }
    }
    let n = ctx.ontology_arenas().concept_count();
    for i in 0..n {
        let cid = ConceptId::new(i);
        let (op_code, role, operands) = {
            let c = ctx.ontology_arenas().concept(cid);
            (
                c.get_operator_code(),
                c.get_role(),
                c.get_operand_list().to_vec(),
            )
        };
        match op_code {
            CCSOME | CCAQSOME | CCALL => {
                // negation = (opCode == CCALL); operand negation = isNegated ^ negation
                let negation = op_code == CCALL;
                let (filler, filler_negated) = operands
                    .first()
                    .map(|op_link| (op_link.target, op_link.negated ^ negation))
                    .unwrap_or((top, negation));
                if roles_with_ranges.contains(&role) {
                    let item = push_role(
                        &mut seeds,
                        &mut role_seed_index,
                        role,
                        filler,
                        filler_negated,
                        true,
                    );
                    existential_successor_seed.push((cid, item));
                } else {
                    push(&mut seeds, &mut seed_index, filler, filler_negated, true);
                }
            }
            CCATLEAST | CCATMOST => {
                // ≥/≤: operand polarity as-is (cpp 2049–2054)
                let (filler, filler_negated) = operands
                    .first()
                    .map(|op_link| (op_link.target, op_link.negated))
                    .unwrap_or((top, false));
                if roles_with_ranges.contains(&role) {
                    let item = push_role(
                        &mut seeds,
                        &mut role_seed_index,
                        role,
                        filler,
                        filler_negated,
                        true,
                    );
                    existential_successor_seed.push((cid, item));
                } else {
                    push(&mut seeds, &mut seed_index, filler, filler_negated, true);
                }
            }
            _ => {}
        }
    }
    let base_seed_count = seeds.len();

    // `extendDisjunctionsCandidateAlternativesItems`, C++ 1153-1268. Konclude
    // does not seed every disjunction in the terminology. It starts from the
    // named/existential items above and adds only reachable disjunctions and
    // their effective alternatives. Auxiliary items are invalid special-item
    // references: substituting through one would conflate an alternative with
    // the class whose pseudo-model caused it to be saturated.
    let mut invalid_special = std::collections::HashSet::new();
    let mut extension_item = 0usize;
    while extension_item < seeds.len() {
        let seed = seeds[extension_item];
        extension_item += 1;
        let seed_concept = ctx.ontology_arenas().concept(seed.concept);
        let mut examine = Vec::new();
        let mut candidate_alternative_extraction = false;
        if !seed.negated && seed_concept.has_class_name() {
            candidate_alternative_extraction = seed_concept.get_operator_code() == CCEQ;
            examine.extend(
                seed_concept
                    .get_operand_list()
                    .iter()
                    .map(|operand| (operand.target, operand.negated)),
            );
        } else {
            examine.push((seed.concept, seed.negated));
        }

        let mut cursor = 0usize;
        while cursor < examine.len() {
            let (concept, negated) = examine[cursor];
            cursor += 1;
            let data = ctx.ontology_arenas().concept(concept);
            let op_code = data.get_operator_code();
            let operands = data.get_operand_list().to_vec();
            let op_count = operands.len();

            if (!negated && (op_code == CCAND || op_code == CCOR && op_count == 1))
                || (negated && (op_code == CCOR || op_code == CCAND && op_count == 1))
            {
                examine.extend(
                    operands
                        .iter()
                        .map(|operand| (operand.target, operand.negated ^ negated)),
                );
            } else if op_code == CCAQCHOOCE {
                for operand in &operands {
                    if negated == operand.negated {
                        examine.push((operand.target, operand.negated));
                    }
                    if candidate_alternative_extraction && negated != operand.negated {
                        examine.push((operand.target, !operand.negated));
                    }
                }
            } else if (negated && ((op_code == CCAND || op_code == CCEQ) && op_count > 1))
                || (!negated && op_code == CCOR)
            {
                for operand in &operands {
                    let operand_negated = operand.negated ^ negated;
                    let operand_data = ctx.ontology_arenas().concept(operand.target);
                    let mut checking_concept = operand.target;
                    let mut checking_negated = operand_negated;
                    if operand_data.get_operator_code() == CCAQCHOOCE {
                        let replacements: Vec<ConceptId> = operand_data
                            .get_operand_list()
                            .iter()
                            .filter(|nested| nested.negated == operand_negated)
                            .map(|nested| nested.target)
                            .collect();
                        if replacements.len() == 1 {
                            checking_concept = replacements[0];
                            checking_negated = false;
                        }
                    }
                    push(
                        &mut seeds,
                        &mut seed_index,
                        checking_concept,
                        checking_negated,
                        false,
                    );
                    // CTotallyPrecomputationThread cpp 1225–1227 keeps the
                    // ordinary special reference for positive named disjuncts.
                    // Only anonymous or negated checking items are invalidated.
                    if !ctx
                        .ontology_arenas()
                        .concept(checking_concept)
                        .has_class_name()
                        || checking_negated
                    {
                        invalid_special.insert((checking_concept, checking_negated));
                    }
                }
                push(&mut seeds, &mut seed_index, concept, negated, false);
                invalid_special.insert((concept, negated));
            } else if ((!negated && op_code == CCALL)
                || (negated && matches!(op_code, CCSOME | CCAQSOME)))
                && candidate_alternative_extraction
            {
                push(&mut seeds, &mut seed_index, concept, !negated, false);
                invalid_special.insert((concept, !negated));
            }
        }
    }

    // analyseConceptSaturationSubsumerExistItems, C++ 1018-1102.
    let named: std::collections::HashSet<ConceptId> = bridged.named.iter().copied().collect();
    let mut special_reference: Vec<Option<usize>> = vec![None; seeds.len()];
    let mut multiple_predecessors = vec![false; seeds.len()];
    let mut indirect_successors = vec![false; seeds.len()];
    let mut exist_references: Vec<Vec<usize>> = vec![Vec::new(); seeds.len()];
    for item in 0..seeds.len() {
        let mut stack = vec![(seeds[item].concept, seeds[item].negated)];
        let mut visited = std::collections::HashSet::new();
        while let Some((concept, negated)) = stack.pop() {
            if !visited.insert((concept, negated)) {
                continue;
            }
            let con = ctx.ontology_arenas().concept(concept);
            let op_code = con.get_operator_code();
            let operands = con.get_operand_list();
            let deterministic = (!negated
                && (matches!(op_code, CCAND | CCSUB | CCEQ)
                    || op_code == CCOR && operands.len() == 1))
                || (negated
                    && (op_code == CCOR || matches!(op_code, CCAND | CCEQ) && operands.len() == 1));
            if !deterministic {
                continue;
            }
            for operand in operands {
                let operand_concept = operand.target;
                let operand_negated = operand.negated ^ negated;
                let operand_data = ctx.ontology_arenas().concept(operand_concept);
                let operand_code = operand_data.get_operator_code();
                if !operand_negated
                    && (matches!(operand_code, CCEQ | CCSUB)
                        || operand_code == CCATOM && named.contains(&operand_concept))
                {
                    if let Some(&reference) = seed_index.get(&(operand_concept, false)) {
                        indirect_successors[reference] = true;
                        if special_reference[item].is_none()
                            && !invalid_special
                                .contains(&(seeds[item].concept, seeds[item].negated))
                        {
                            special_reference[item] = Some(reference);
                        } else {
                            multiple_predecessors[item] = true;
                        }
                    }
                } else if (!operand_negated && matches!(operand_code, CCAND | CCAQAND))
                    || (operand_negated && operand_code == CCOR)
                {
                    if operand_data.get_operand_list().len() > 1 {
                        multiple_predecessors[item] = true;
                    }
                    stack.push((operand_concept, operand_negated));
                } else if (!operand_negated && matches!(operand_code, CCSOME | CCAQSOME))
                    || (operand_negated && operand_code == CCALL)
                {
                    let role = operand_data.get_role();
                    let filler = operand_data
                        .get_operand_list()
                        .first()
                        .map(|link| (link.target, link.negated ^ operand_negated))
                        .unwrap_or((top, false));
                    let reference = if roles_with_ranges.contains(&role) {
                        role_seed_index.get(&(role, filler.0, filler.1))
                    } else {
                        seed_index.get(&filler)
                    };
                    if let Some(&reference) = reference {
                        exist_references[item].push(reference);
                    }
                    multiple_predecessors[item] = true;
                } else if (!negated && operand_code == CCATLEAST)
                    || (negated && operand_code == CCATMOST)
                {
                    let role = operand_data.get_role();
                    let filler = operand_data
                        .get_operand_list()
                        .first()
                        .map(|link| (link.target, link.negated))
                        .unwrap_or((top, false));
                    let reference = if roles_with_ranges.contains(&role) {
                        role_seed_index.get(&(role, filler.0, filler.1))
                    } else {
                        seed_index.get(&filler)
                    };
                    if let Some(&reference) = reference {
                        exist_references[item].push(reference);
                    }
                    multiple_predecessors[item] = true;
                } else if operand_code == CCAQCHOOCE {
                    for nested in operand_data.get_operand_list() {
                        if operand_negated != nested.negated {
                            continue;
                        }
                        let nested_data = ctx.ontology_arenas().concept(nested.target);
                        match nested_data.get_operator_code() {
                            CCAQSOME => {
                                if let Some(filler) = nested_data.get_operand_list().first() {
                                    let role = nested_data.get_role();
                                    let reference = if roles_with_ranges.contains(&role) {
                                        role_seed_index.get(&(role, filler.target, filler.negated))
                                    } else {
                                        seed_index.get(&(filler.target, filler.negated))
                                    };
                                    if let Some(&reference) = reference {
                                        exist_references[item].push(reference);
                                    }
                                }
                                multiple_predecessors[item] = true;
                            }
                            CCAQAND => {
                                if operand_data.get_operand_list().len() > 1 {
                                    multiple_predecessors[item] = true;
                                }
                                stack.push((nested.target, false));
                            }
                            _ => {}
                        }
                    }
                } else {
                    multiple_predecessors[item] = true;
                }
            }
        }
        exist_references[item].sort_unstable();
        exist_references[item].dedup();
    }

    // C++ propagateSubsumerItemFlag / propagateExistInitializationFlag.
    for item in 0..seeds.len() {
        if indirect_successors[item] {
            let mut next = special_reference[item];
            while let Some(reference) = next {
                if indirect_successors[reference] {
                    break;
                }
                indirect_successors[reference] = true;
                next = special_reference[reference];
            }
        }
        if seeds[item].potentially_exist {
            let mut next = special_reference[item];
            while let Some(reference) = next {
                if seeds[reference].potentially_exist {
                    break;
                }
                seeds[reference].potentially_exist = true;
                next = special_reference[reference];
            }
        }
    }

    // Diagnostic ablation for comparing Konclude's tag-ordered special-reference
    // choice with a bridge build whose independently assigned concept tags choose
    // another deterministic subsumer. Format: `source-tag:reference-tag`.
    if let Ok(override_spec) = std::env::var("KM_SAT_SPECIAL_REF_OVERRIDE") {
        for pair in override_spec.split(',') {
            let Some((source, reference)) = pair.split_once(':') else {
                continue;
            };
            let (Ok(source_tag), Ok(reference_tag)) =
                (source.parse::<Cint64>(), reference.parse::<Cint64>())
            else {
                continue;
            };
            let source_item = seeds.iter().position(|seed| {
                !seed.negated
                    && ctx
                        .ontology_arenas()
                        .concept(seed.concept)
                        .get_concept_tag()
                        == source_tag
            });
            let reference_item = seeds.iter().position(|seed| {
                !seed.negated
                    && ctx
                        .ontology_arenas()
                        .concept(seed.concept)
                        .get_concept_tag()
                        == reference_tag
            });
            if let (Some(source_item), Some(reference_item)) = (source_item, reference_item) {
                special_reference[source_item] = Some(reference_item);
                multiple_predecessors[source_item] = true;
                eprintln!(
                    "SAT-SPECIAL-REF-OVERRIDE source-tag={} reference-tag={}",
                    source_tag, reference_tag,
                );
            }
        }
    }

    // Dependency-first equivalent of orderItemsSaturationTesting.
    fn order_item(
        item: usize,
        special_reference: &[Option<usize>],
        exist_references: &[Vec<usize>],
        state: &mut [u8],
        order: &mut Vec<usize>,
    ) {
        if state[item] == 2 {
            return;
        }
        if state[item] == 1 {
            return;
        }
        state[item] = 1;
        if let Some(reference) = special_reference[item] {
            order_item(reference, special_reference, exist_references, state, order);
        }
        // C++ pushes the list in forward order onto a stack, so the last
        // existential reference is ordered first.
        for &reference in exist_references[item].iter().rev() {
            order_item(reference, special_reference, exist_references, state, order);
        }
        state[item] = 2;
        order.push(item);
    }
    let mut order = Vec::with_capacity(seeds.len());
    let mut order_state = vec![0u8; seeds.len()];
    // Konclude starts with real non-existential leaves, then existential
    // leaves, and only then sweeps the remaining components.
    for item in 0..seeds.len() {
        if !indirect_successors[item] && !seeds[item].potentially_exist {
            order_item(
                item,
                &special_reference,
                &exist_references,
                &mut order_state,
                &mut order,
            );
        }
    }
    for item in 0..seeds.len() {
        if !indirect_successors[item] && seeds[item].potentially_exist {
            order_item(
                item,
                &special_reference,
                &exist_references,
                &mut order_state,
                &mut order,
            );
        }
    }
    for item in 0..seeds.len() {
        order_item(
            item,
            &special_reference,
            &exist_references,
            &mut order_state,
            &mut order,
        );
    }

    // Allocate every ontology item before wiring cross-item references.
    let mut onto_items = vec![SaturationConceptReferenceLinkingId::NONE; seeds.len()];
    for (item_index, seed) in seeds.iter().enumerate() {
        let concept = seed.concept;
        let negation = seed.negated;
        if seed.role_ranges.is_some() {
            // `getSaturationRoleSuccessorConceptDataItem` stores this item in
            // the role/concept/negation hash only. It must not occupy the
            // filler's ordinary positive/negative reference slot.
            let onto_item = {
                let arenas = ctx.ontology_arenas_mut();
                let mut item = SaturationConceptReferenceLinking::new();
                item.init_concept_saturation_testing_item(concept, negation, seed.role_ranges);
                item.set_potentially_exist_initialization_concept(seed.potentially_exist);
                if arenas.role(seed.role_ranges).is_data_role() {
                    item.set_data_range_concept(true);
                }
                arenas.alloc_saturation_concept_reference_linking(item)
            };
            onto_items[item_index] = onto_item;
            continue;
        }
        // Ensure the concept's process data + saturation reference-linking data.
        let con_proc_data = {
            let concept_data = ctx.ontology_arenas().concept(concept).get_concept_data();
            if concept_data == super::model::substrate::INVALID {
                let arenas = ctx.ontology_arenas_mut();
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(concept).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            }
        };
        let mut ref_linking_data = ctx
            .ontology_arenas()
            .concept_process_data(con_proc_data)
            .get_concept_reference_linking();
        if ref_linking_data.is_none() {
            let arenas = ctx.ontology_arenas_mut();
            ref_linking_data = arenas.alloc_concept_saturation_reference_linking_data(
                ConceptSaturationReferenceLinkingData::new(),
            );
            arenas
                .concept_process_data_mut(con_proc_data)
                .set_concept_reference_linking(ref_linking_data);
        }
        // One item per (concept, polarity): skip if already wired.
        let existing = ctx
            .ontology_arenas()
            .concept_saturation_reference_linking_data(ref_linking_data)
            .get_concept_saturation_reference_linking_data(negation);
        if existing.is_some() {
            onto_items[item_index] = existing;
            continue;
        }
        // Ontology-side item (CSaturationConceptDataItem).
        let onto_item = {
            let arenas = ctx.ontology_arenas_mut();
            let mut item = SaturationConceptReferenceLinking::new();
            item.init_concept_saturation_testing_item(concept, negation, RoleId::NONE);
            item.set_potentially_exist_initialization_concept(seed.potentially_exist);
            let onto_item = arenas.alloc_saturation_concept_reference_linking(item);
            arenas
                .concept_saturation_reference_linking_data_mut(ref_linking_data)
                .set_saturation_reference_linking_data(onto_item, negation);
            onto_item
        };
        onto_items[item_index] = onto_item;
    }

    // Wire each restriction to the role-specific item before any saturation
    // node is constructed. This is the exact reference read first by
    // `createSuccessorForConcept`; ordinary filler lookup remains its fallback.
    for (restriction, item_index) in existential_successor_seed {
        if item_index == usize::MAX || onto_items[item_index].is_none() {
            continue;
        }
        let con_proc_data = {
            let concept_data = ctx
                .ontology_arenas()
                .concept(restriction)
                .get_concept_data();
            if concept_data == super::model::substrate::INVALID {
                let arenas = ctx.ontology_arenas_mut();
                let fresh = arenas.alloc_concept_process_data(ConceptProcessData::new());
                arenas.concept_mut(restriction).set_concept_data(fresh.raw);
                fresh
            } else {
                super::model::concept_process::ConceptProcessDataId::new(concept_data)
            }
        };
        let mut ref_linking_data = ctx
            .ontology_arenas()
            .concept_process_data(con_proc_data)
            .get_concept_reference_linking();
        if ref_linking_data.is_none() {
            let arenas = ctx.ontology_arenas_mut();
            ref_linking_data = arenas.alloc_concept_saturation_reference_linking_data(
                ConceptSaturationReferenceLinkingData::new(),
            );
            arenas
                .concept_process_data_mut(con_proc_data)
                .set_concept_reference_linking(ref_linking_data);
        }
        let current = ctx
            .ontology_arenas()
            .concept_saturation_reference_linking_data(ref_linking_data)
            .get_existential_successor_concept_saturation_reference_linking_data();
        if current.is_none() {
            ctx.ontology_arenas_mut()
                .concept_saturation_reference_linking_data_mut(ref_linking_data)
                .set_existential_successor_concept_saturation_reference_linking_data(
                    onto_items[item_index],
                );
        }
    }

    // Reference mode, C++ 2190-2205. Trigger-host concepts conservatively use
    // COPY, matching the triggerImpHash guard in Konclude.
    for item in 0..seeds.len() {
        let Some(reference) = special_reference[item] else {
            continue;
        };
        let contains_trigger = ctx
            .ontology_arenas()
            .concept(seeds[item].concept)
            .get_operand_list()
            .iter()
            .any(|operand| {
                ctx.ontology_arenas()
                    .concept(operand.target)
                    .get_operator_code()
                    == CCIMPLTRIG
            });
        let mode = if !seeds[item].potentially_exist
            && !multiple_predecessors[item]
            && !contains_trigger
        {
            SATURATION_SUBSTITUTE_MODE
        } else {
            SATURATION_COPY_MODE
        };
        ctx.ontology_arenas_mut()
            .saturation_concept_reference_linking_mut(onto_items[item])
            .set_special_item_reference(onto_items[reference])
            .set_special_item_reference_mode(mode);
    }

    // Generator construction loop. Build all nodes first, then queue them in
    // dependency order; databox insertion is head-first, hence reverse insert.
    let mut next_indi_id: Cint64 = 1;
    let mut linkers = vec![IndividualSaturationProcessNodeLinkerId::NONE; seeds.len()];
    // `extendApproximatedSaturationCalculationJobConstruction` prepends each
    // construct. The task generator therefore allocates nodes in reverse
    // ordered-item order, giving referenced dependencies larger individual
    // IDs. Successor-extension processing is keyed by negative individual ID,
    // so this reversal is required to process dependencies before dependents.
    for &item_index in order.iter().rev() {
        let seed = seeds[item_index];
        let concept = seed.concept;
        let negation = seed.negated;
        let onto_item = onto_items[item_index];
        // Process-side item mirror + the node (generator cpp 108–135).
        let ext_item = {
            let mut ext = ExtendedConceptReferenceLinkingData::new();
            ext.init_concept_saturation_testing_item(concept, negation, seed.role_ranges);
            ext.set_concept_reference_linking(onto_item.raw);
            ctx.process_context_mut()
                .alloc_extended_con_ref_linking_data(ext)
        };
        let individual_id = next_indi_id;
        next_indi_id += 1;
        let node = ctx
            .process_context_mut()
            .alloc_sat_node(IndividualSaturationProcessNode::new(
                super::model::substrate::INVALID,
            ));
        ctx.process_context_mut()
            .sat_node_mut(node)
            .init_individual_saturation_process_node(individual_id, ext_item, Id::NONE);
        ctx.ontology_arenas_mut()
            .saturation_concept_reference_linking_mut(onto_item)
            .set_individual_process_node_for_concept(node);
        ctx.processing_data_box_mut()
            .individual_saturation_process_node_vector(true)
            .expect("create=true yields CIndividualSaturationProcessNodeVector")
            .set_data(individual_id, node);
        // indiProcNodeLinker: initProcessNodeLinker(node, processing=true) +
        // dataBox->addIndividualSaturationProcessNodeLinker (generator cpp 129–134).
        let linker = ctx
            .process_context_mut()
            .sat_node_individual_saturation_process_node_linker(node, true);
        ctx.process_context_mut()
            .indi_sat_process_node_linker_mut(linker)
            .set_processing_queued(true);
        linkers[item_index] = linker;
    }
    // The generator also prepends each allocated linker to the processing
    // list. Adding the reverse construction sequence reproduces the final
    // dependency-first list.
    for &item_index in order.iter().rev() {
        ctx.processing_data_box_mut()
            .add_individual_saturation_process_node_linker(linkers[item_index]);
    }
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        let substitute_count = (0..seeds.len())
            .filter(|&item| {
                ctx.ontology_arenas()
                    .saturation_concept_reference_linking(onto_items[item])
                    .get_special_reference_mode()
                    == SATURATION_SUBSTITUTE_MODE
            })
            .count();
        let copy_count = (0..seeds.len())
            .filter(|&item| {
                ctx.ontology_arenas()
                    .saturation_concept_reference_linking(onto_items[item])
                    .get_special_reference_mode()
                    == SATURATION_COPY_MODE
            })
            .count();
        eprintln!(
            "BRIDGE-SATURATION-SEEDS: base={} extended={} invalid-special={} substitute={} copy={}",
            base_seed_count,
            seeds.len(),
            invalid_special.len(),
            substitute_count,
            copy_count,
        );
    }
}

/// Per-classification saturation outcome, extracted into plain data so the
/// probe env's resets cannot invalidate it.
pub struct SaturationOutcome {
    /// Per named index: `Some(true)` = UNSAT-certain, `Some(false)` =
    /// SAT-certain, `None` = unknown (probe needed).
    pub sat_verdict: Vec<Option<bool>>,
    /// Per named index: the COMPLETE certain-subsumer set (named indices,
    /// self excluded) — present exactly when the node is sufficient
    /// (SAT-certain), per `CPrecomputedSaturationSubsumerExtractor`.
    pub certain_subsumers: Vec<Option<Vec<usize>>>,
    /// Sound positive named labels for every processed saturation node,
    /// including insufficient nodes. Insufficiency means incomplete, not
    /// incorrect; Konclude seeds KPSet known subsumers from these labels.
    pub known_subsumers: Vec<Vec<usize>>,
}

/// Resolve Konclude's saturation substitute chain and report the named
/// concepts carried by its intermediate nodes.
///
/// This is the first loop in
/// `CPrecomputedSaturationSubsumerExtractor::extractSubsumers`: the base node
/// is excluded, every non-terminal substitute node contributes its positive
/// class concept when it is not a role-range test or the queried concept, and
/// the terminal node is returned for the ordinary label extraction below.
fn resolve_saturation_substitute_chain(
    ctx: &CalculationAlgorithmContextBase,
    base_node: super::process::SatNodeId,
    queried_concept: ConceptId,
    named_index: &std::collections::HashMap<ConceptId, usize>,
    subsumers: &mut Vec<usize>,
) -> super::process::SatNodeId {
    let mut resolved = base_node;
    while ctx
        .process_context()
        .sat_node(resolved)
        .has_substitute_individual_node()
    {
        if resolved != base_node {
            let reference = ctx
                .process_context()
                .sat_node(resolved)
                .get_saturation_concept_reference_linking();
            if reference.is_some() {
                let item = ctx
                    .process_context()
                    .extended_con_ref_linking_data(reference);
                let concept = item.get_saturation_concept();
                if !item.get_saturation_negation()
                    && item.get_saturation_role_ranges().is_none()
                    && concept != queried_concept
                {
                    if let Some(&index) = named_index.get(&concept) {
                        subsumers.push(index);
                    }
                }
            }
        }
        resolved = ctx
            .process_context()
            .sat_node(resolved)
            .get_substitute_individual_node();
    }
    resolved
}

/// `CPrecomputedSaturationSubsumerExtractor::getConceptFlags` + `extractSubsumers`
/// over the saturated bridge env: follow the POSITIVE node (substitute-chain
/// resolved), read INDIRECT flags of base + resolved node —
/// CLASHED ⇒ UNSAT-certain; ¬INSUFFICIENT ∧ ¬UNPROCESSED and no problematic
/// EQ-candidate descriptor ⇒ SAT-certain with the label's non-negated named
/// entries as the exact subsumer set; anything else ⇒ unknown.
fn extract_saturation_outcome(
    ctx: &mut CalculationAlgorithmContextBase,
    bridged: &Bridged,
) -> SaturationOutcome {
    use super::process::sat_node::IndividualSaturationProcessNodeStatusFlags as F;
    let n_named = bridged.named.len();
    let named_index: std::collections::HashMap<ConceptId, usize> = bridged
        .named
        .iter()
        .enumerate()
        .map(|(i, &c)| (c, i))
        .collect();
    let mut sat_verdict: Vec<Option<bool>> = vec![None; n_named];
    let mut certain_subsumers: Vec<Option<Vec<usize>>> = vec![None; n_named];
    let mut known_subsumers: Vec<Vec<usize>> = vec![Vec::new(); n_named];
    let mut unknown_no_node = 0usize;
    let mut unknown_insufficient = 0usize;
    let mut unknown_unprocessed = 0usize;
    let mut unknown_eq_candidate = 0usize;
    let trust_insufficient = std::env::var_os("KM_HT_TRUST_INSUFFICIENT").is_some();
    for (i, &named) in bridged.named.iter().enumerate() {
        let base_node =
            super::saturation::algorithm::SaturationTaskHandleAlgorithm::s07_concept_reference_node(
                named, false, ctx,
            );
        if base_node.is_none() {
            unknown_no_node += 1;
            continue;
        }
        // `extractSubsumers` reports positive named concepts attached to
        // intermediate substitute nodes before reading the terminal label.
        let mut subs: Vec<usize> = Vec::new();
        let resolved =
            resolve_saturation_substitute_chain(ctx, base_node, named, &named_index, &mut subs);
        let read = |node: super::process::SatNodeId,
                    ctx: &CalculationAlgorithmContextBase|
         -> (bool, bool, bool, bool) {
            let sat_node = ctx.process_context().sat_node(node);
            let ind = sat_node.indirect_status_flags.get_flags();
            let dir = sat_node.direct_status_flags.get_flags();
            (
                ind & F::INDSATFLAGCLASHED != 0,
                ind & F::INDSATFLAGINSUFFICIENT != 0,
                ind & F::INDSATFLAGUNPROCESSED != 0,
                dir & F::INDSATFLAGEQCANDPROPLEMATIC != 0,
            )
        };
        let (b_clash, b_insuf, b_unproc, _b_eqprob) = read(base_node, ctx);
        let (r_clash, r_insuf, r_unproc, r_eqprob) = read(resolved, ctx);
        if std::env::var_os("KM_SAT_DEBUG").is_some() {
            eprintln!(
                "SAT-SUBJ {} concept={:?} base={:?} resolved={:?} b_clash={} r_clash={}",
                i, named, base_node, resolved, b_clash, r_clash
            );
        }
        let clashed = b_clash || r_clash;
        let insufficient = b_insuf || r_insuf;
        let unprocessed = b_unproc || r_unproc;
        // extractSubsumers (cpp 40–130): non-negated class-named label entries
        // are sound known subsumers even when the node is insufficient.
        let mut eq_candidate_present = false;
        let label = ctx
            .process_context()
            .sat_node(resolved)
            .reapply_con_sat_label_set;
        if label.is_some() {
            let mut des = ctx
                .process_context()
                .reapply_con_sat_label_set(label)
                .get_concept_saturation_description_linker();
            while des.is_some() {
                let (concept, negated) = {
                    let d = ctx.process_context().con_sat_desc(des);
                    (d.get_concept(), d.get_negation())
                };
                let op_code = ctx.ontology_arenas().concept(concept).get_operator_code();
                eq_candidate_present |= op_code == op::CCEQCAND;
                if !negated {
                    if let Some(&idx) = named_index.get(&concept) {
                        if idx != i {
                            subs.push(idx);
                        }
                    }
                }
                des = ctx
                    .process_context()
                    .con_sat_desc(des)
                    .get_next_concept_desciptor();
            }
        }
        subs.sort_unstable();
        subs.dedup();
        known_subsumers[i] = subs.clone();
        if clashed {
            sat_verdict[i] = Some(true);
            continue;
        }
        if insufficient && !trust_insufficient || unprocessed || eq_candidate_present && r_eqprob {
            unknown_insufficient += usize::from(insufficient && !trust_insufficient);
            unknown_unprocessed += usize::from(unprocessed);
            unknown_eq_candidate += usize::from(eq_candidate_present && r_eqprob);
            continue; // unknown — probe needed
        }
        sat_verdict[i] = Some(false);
        certain_subsumers[i] = Some(subs);
    }
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        eprintln!(
            "BRIDGE-SATURATION-UNKNOWN: no-node={} insufficient={} unprocessed={} eq-candidate={}",
            unknown_no_node, unknown_insufficient, unknown_unprocessed, unknown_eq_candidate,
        );
    }
    SaturationOutcome {
        sat_verdict,
        certain_subsumers,
        known_subsumers,
    }
}

/// Saturate the bridged ontology once (dedicated env — the probe env and its
/// resets are untouched) and extract the verdicts. `None` when the input is
/// outside the bridge fragment.
pub fn bridged_saturate(tin: &TInput) -> Option<SaturationOutcome> {
    if !tin.nominals.is_empty() {
        return None;
    }
    let (_completion_algo, mut ctx, bridged) = fresh_bridge_env(tin);
    if bridged.unsupported > 0 {
        return None;
    }
    if !run_bridged_saturation(&mut ctx, &bridged) {
        return None;
    }
    Some(extract_saturation_outcome(&mut ctx, &bridged))
}

/// Run the production approximation saturation ON the given bridge env
/// (preprocess + seeds + drive). Returns false on a budget overrun: unfinished
/// queues may hold unchecked critical concepts, so no per-node flags are
/// trustworthy — the caller must discard the pass (no verdict extraction, no
/// saturation-node coupling). The saturation NODES remain in the env's arenas
/// either way (the concept→saturation reference linkings installed by the
/// seeds point at them; see `reset_probe_env`'s saturation carry).
fn run_bridged_saturation(ctx: &mut CalculationAlgorithmContextBase, bridged: &Bridged) -> bool {
    let mut sat_algo = super::saturation::algorithm::SaturationTaskHandleAlgorithm::new();
    configure_production_saturation(&mut sat_algo);
    extract_propagation_into_creation_direction(ctx);
    build_saturation_seeds(ctx, bridged);
    if !sat_algo.run_saturation_on(ctx) {
        return false;
    }
    if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
        eprintln!(
            "SAT-STATS: insufficient all={} atmost={} or={} eqcand={} value={} nominal={}",
            sat_algo.insufficient_all_count,
            sat_algo.insufficient_atmost_count,
            sat_algo.insufficient_or_count,
            sat_algo.insufficient_eqcand_count,
            sat_algo.insufficient_value_count,
            sat_algo.insufficient_nominal_count,
        );
    }
    if std::env::var_os("KM_SAT_DEBUG").is_some() {
        debug_dump_saturation_nodes(ctx);
    }
    true
}

/// Temporary diagnostic (env `KM_SAT_DEBUG=1`): per saturation node, dump the
/// completion state, direct/indirect flag words and the full saturated label
/// (concept id, op code, negation).
fn debug_dump_saturation_nodes(ctx: &CalculationAlgorithmContextBase) {
    let n = ctx.process_context().sat_node_count();
    for i in 0..n {
        let node = super::process::SatNodeId::new(i as Cint64);
        let sat_node = ctx.process_context().sat_node(node);
        let label = sat_node.reapply_con_sat_label_set;
        eprintln!(
            "SAT-NODE {}: indi={} completed={} dir={:#x} ind={:#x} subst={:?}",
            i,
            sat_node.get_individual_id(),
            sat_node.is_completed(),
            sat_node.direct_status_flags.get_flags(),
            sat_node.indirect_status_flags.get_flags(),
            sat_node.get_substitute_individual_node(),
        );
        if label.is_some() {
            let ls = ctx.process_context().reapply_con_sat_label_set(label);
            let mut entries: Vec<(Cint64, String)> = Vec::new();
            for (tag, data) in ls
                .concept_des_dep_hash
                .iter()
                .chain(ls.additional_concept_des_dep_hash.iter())
            {
                let des = data.con_sat_des;
                if des.is_some() {
                    let c = ctx.process_context().con_sat_desc(des).get_concept();
                    let neg = ctx.process_context().con_sat_desc(des).get_negation();
                    let op = ctx.ontology_arenas().concept(c).get_operator_code();
                    entries.push((*tag, format!("c{}(op{},neg={})", c.index(), op, neg)));
                } else {
                    entries.push((*tag, "reapply-only".to_string()));
                }
            }
            entries.sort();
            for (tag, s) in entries {
                eprintln!("    tag {} -> {}", tag, s);
            }
        }
    }
}

/// Deterministic named hierarchy already present in Konclude's CCSUB/CCEQ
/// terminology before classification. A named subclass implies every named
/// top-level conjunct of its definition; closing those edges transitively is
/// a sound known-subsumer seed for KPSet and requires no tableau probe.
fn source_named_subsumer_closure(tin: &TInput) -> std::collections::HashSet<(usize, usize)> {
    let index: HashMap<&str, usize> = tin
        .concepts
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
    fn collect<'a>(concept: &'a SourceConcept, out: &mut Vec<&'a str>) {
        match concept {
            SourceConcept::Name(name) => out.push(name.as_str()),
            SourceConcept::And(operands) => {
                for operand in operands {
                    collect(operand, out);
                }
            }
            _ => {}
        }
    }
    let mut direct: Vec<Vec<usize>> = vec![Vec::new(); tin.concepts.len()];
    let mut add = |left: &SourceConcept, right: &SourceConcept| {
        let SourceConcept::Name(left) = left else {
            return;
        };
        let Some(&sub) = index.get(left.as_str()) else {
            return;
        };
        let mut names = Vec::new();
        collect(right, &mut names);
        for name in names {
            if let Some(&sup) = index.get(name) {
                if sup != sub {
                    direct[sub].push(sup);
                }
            }
        }
    };
    for axiom in &tin.source_axioms {
        match axiom.kind {
            crate::json_io::SourceAxiomKind::SubClass => add(&axiom.left, &axiom.right),
            crate::json_io::SourceAxiomKind::Equivalent => {
                add(&axiom.left, &axiom.right);
                add(&axiom.right, &axiom.left);
            }
            crate::json_io::SourceAxiomKind::Disjoint => {}
        }
    }
    let mut closure = std::collections::HashSet::new();
    for sub in 0..direct.len() {
        let mut stack = direct[sub].clone();
        while let Some(sup) = stack.pop() {
            if closure.insert((sub, sup)) {
                stack.extend(direct[sup].iter().copied());
            }
        }
    }
    closure
}

/// Production classification of a `TInput` over the konclude_ht bridge.
///
/// Per subject: model read-off when the saturation was deterministic
/// (authoritative — the canonical model IS the subsumer set), else candidate
/// extraction + pairwise `bridged_unsat(s ⊓ ¬c)` verification (label ABSENCE
/// in a saturated clash-free graph is a countermodel even on a
/// non-deterministic drive, so the candidate positives are a complete
/// filter; only presences need verification).
///
/// Returns `None` (DEFER — the caller must fall back to a sound+complete
/// arm) when the answer would not be both sound and complete:
/// - the encoder could not express every clause (`unsupported > 0`);
/// - the input carries nominals/ABox content (not bridged);
/// - a subject still lacks a verdict after every retry round (a STOPped
///   drive/probe defers the SUBJECT first; only subjects that exhaust the
///   escalated budgets defer the whole classification).
///
/// Per-probe budget: `KM_BRIDGE_PROBE_BUDGET_S` (default 10 s) for the first
/// round; deferred subjects are retried with the budget escalated ×4 per
/// round for `KM_BRIDGE_RETRY_ROUNDS` (default 2) extra rounds — so one
/// pathological subject costs bounded time while the cheap bulk completes,
/// instead of the first budget-STOP discarding all finished work.
pub fn bridged_classify(tin: &TInput) -> Option<BridgedClassification> {
    // Saturation-first probe answering (task #23, opt-in KM_HT_SATURATION=1)
    // + the saturation-node coupling into the residue probes (task #24 wave 2,
    // opt-in KM_HT_SATCACHE=1 on top). The coupling stays OPT-IN because
    // without the extension-resolving refinement (needs the ext machinery,
    // currently unsound/off) the replayed labels under-approximate the
    // ∀-restricted successors, establish fails there, and the enlarged labels
    // measurably POISON probes earlier (12653: permanent defer at subject 1
    // vs 14 plain). Re-evaluate the default after the ext-machinery audit.
    // Trigger absorption is designed to make the non-branching saturation
    // residue filter effective, so enabling it also enables this pre-pass. The
    // legacy explicit flag remains available for absorption-off diagnostics.
    let use_saturation = std::env::var_os("KM_HT_NO_SATURATION").is_none()
        && (std::env::var_os("KM_HT_SATURATION").is_some()
            || std::env::var_os("KM_TRIGGER_ABSORB").is_some());
    let use_satcache = use_saturation
        && std::env::var_os("KM_HT_NO_SATCACHE").is_none()
        && (std::env::var_os("KM_HT_SATCACHE").is_some()
            || std::env::var_os("KM_TRIGGER_ABSORB").is_some());
    bridged_classify_opts(tin, use_saturation, use_satcache)
}

/// The env-independent core of [`bridged_classify`] — `use_saturation` answers
/// whole subjects from a pre-probe saturation pass, `use_satcache` additionally
/// arms the saturation-node coupling (expand-from-saturation + caching-blocking,
/// Konclude's production completion profile) inside the residue probes.
pub fn bridged_classify_opts(
    tin: &TInput,
    use_saturation: bool,
    use_satcache: bool,
) -> Option<BridgedClassification> {
    if !tin.nominals.is_empty() {
        return None;
    }
    let n_named = tin.concepts.len();
    // The classification UNIVERSE: real named classes only. `tin.concepts`
    // also carries frontend-SYNTHETIC concepts (recognition markers `Q_n`,
    // `aux_`/`def_` definers, `__`-markers) — the signature never contains
    // them, and treating them as candidate supers is ruinous: refuting one
    // marker "candidate" costs a full SAT search per subject (measured on
    // ore_ont_12653: every subject burnt its whole probe budget refuting
    // Q_n markers; with the universe filter the candidate sets collapse to
    // the real taxonomy).
    let universe: std::collections::HashSet<usize> = tin
        .concepts
        .iter()
        .enumerate()
        .filter(|(_, n)| {
            !crate::orchestrate::cb_to_ht::is_internal(n)
                && !crate::orchestrate::cb_to_ht::is_bottom(n)
        })
        .map(|(i, _)| i)
        .collect();
    let subjects: Vec<usize> = if tin.queries.is_empty() {
        let mut v: Vec<usize> = universe.iter().copied().collect();
        v.sort_unstable();
        v
    } else {
        tin.queries.iter().map(|&q| q as usize).collect()
    };
    let progress = std::env::var_os("KM_BRIDGE_PROGRESS").is_some();
    let mut out = BridgedClassification {
        unsatisfiable: Vec::new(),
        subsumptions: Vec::new(),
    };
    let subject_set: std::collections::HashSet<usize> = subjects.iter().copied().collect();
    let mut saturation_known_pairs = source_named_subsumer_closure(tin);
    saturation_known_pairs.retain(|(sub, sup)| subject_set.contains(sub) && universe.contains(sup));
    out.subsumptions
        .extend(saturation_known_pairs.iter().copied());
    // ONE bridged environment for the whole classification (#13): built once,
    // reset to pristine between probes (`reset_probe_env`), instead of an
    // O(TBox) rebuild per subject AND per pairwise probe.
    let (mut algo, mut ctx, bridged) = fresh_bridge_env(tin);
    if bridged.unsupported > 0 {
        return None;
    }
    let base_budget = std::env::var("KM_BRIDGE_PROBE_BUDGET_S")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(10);
    let retry_rounds = std::env::var("KM_BRIDGE_RETRY_ROUNDS")
        .ok()
        .and_then(|s| s.parse::<u32>().ok())
        .unwrap_or(2);
    let mut pending: Vec<usize> = subjects;
    let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
    let mut kpset_state: Option<SynchronousKPSetClassState> = None;
    // Saturation-first probe answering (task #23): saturate the bridged
    // ontology ONCE in an independent calculation task and pass only the
    // extracted flags/subsumers into classification. Only explicit SATCACHE
    // coupling keeps the saturation nodes in the completion environment.
    // This mirrors Konclude's task boundary; carrying uncoupled saturation
    // process state made 541 completion probes search a different graph.
    // Then answer whole subjects from certain
    // verdicts: UNSAT-certain subjects land in `unsatisfiable`, SAT-certain
    // subjects with a sufficient label get their COMPLETE subsumer set from
    // the saturated label (Konclude's CPrecomputedSaturationSubsumerExtractor
    // consumption). Only the UNKNOWN residue runs the completion probes,
    // with the coupling (u08/u17/u22) armed when `use_satcache`.
    let mut saturation_ran = false;
    let mut satcache_active = false;
    if use_saturation {
        let t_sat = std::time::Instant::now();
        let mut saturation_complete = true;
        let outcome = if use_satcache {
            saturation_complete = run_bridged_saturation(&mut ctx, &bridged);
            // An interrupted approximation pass still contains only monotonic
            // consequences. Extracted positive labels and clash flags are
            // sound KPSet seeds; the completed-node guard prevents unfinished
            // nodes from becoming SAT-certain. Do not couple this partial graph
            // into completion below.
            Some(extract_saturation_outcome(&mut ctx, &bridged))
        } else {
            bridged_saturate(tin)
        };
        if let Some(outcome) = outcome {
            if use_satcache && std::env::var_os("KM_SAT_DEBUG").is_some() {
                for (i, c) in bridged.named.iter().enumerate() {
                    eprintln!(
                        "SAT-NAME {} concept={:?} {}",
                        i,
                        c,
                        tin.concepts.get(i).map(|n| n.as_str()).unwrap_or("?")
                    );
                }
                let n = ctx.ontology_arenas().concept_count();
                for ci in 0..n {
                    let cid = super::model::ConceptId::new(ci);
                    let c = ctx.ontology_arenas().concept(cid);
                    let ops: Vec<String> = c
                        .get_operand_list()
                        .iter()
                        .map(|l| format!("{}{:?}", if l.negated { "!" } else { "" }, l.target))
                        .collect();
                    eprintln!(
                        "SAT-CONCEPT {:?} op={} tag={} role={:?} param={} operands=[{}]",
                        cid,
                        c.get_operator_code(),
                        c.get_concept_tag(),
                        c.get_role(),
                        c.get_parameter(),
                        ops.join(",")
                    );
                }
            }
            for &s in &pending {
                for &c in &outcome.known_subsumers[s] {
                    if c != s && universe.contains(&c) && saturation_known_pairs.insert((s, c)) {
                        out.subsumptions.push((s, c));
                    }
                }
            }
            let mut answered_unsat = 0usize;
            let mut answered_sat = 0usize;
            pending.retain(|&s| match outcome.sat_verdict[s] {
                Some(true) => {
                    if std::env::var_os("KM_SAT_DEBUG").is_some() {
                        eprintln!(
                            "SAT-UNSAT-VERDICT subject {} ({})",
                            s,
                            tin.concepts.get(s).map(|n| n.as_str()).unwrap_or("?")
                        );
                    }
                    out.unsatisfiable.push(s);
                    answered_unsat += 1;
                    false
                }
                Some(false) => {
                    if outcome.certain_subsumers[s].is_some() {
                        answered_sat += 1;
                        false
                    } else {
                        true
                    }
                }
                None => true,
            });
            if std::env::var_os("KM_BRIDGE_SAT_RESIDUE").is_some() {
                for &subject in &pending {
                    eprintln!(
                        "BRIDGE-SATURATION-RESIDUE subject={subject} class={}",
                        tin.concepts.get(subject).map(String::as_str).unwrap_or("?")
                    );
                }
            }
            // Konclude does not run the insufficient residue in signature
            // order.  Its KPSet classifier builds the predecessor graph from
            // every sound saturation label, then schedules root classes
            // before their descendants.  The bridge executes jobs
            // synchronously, but consumes the same production KPSet order.
            let state = classifier.initialize_synchronous_kpset_from_saturation_data(
                &bridged.named,
                &outcome.sat_verdict,
                &outcome.certain_subsumers,
                &outcome.known_subsumers,
                &pending,
                ctx.ontology_arenas().concepts(),
            );
            pending = state.ordered_subjects.clone();
            kpset_state = Some(state);
            saturation_ran = use_satcache && saturation_complete;
            satcache_active = use_satcache && saturation_complete;
            if progress {
                eprintln!(
                    "BRIDGE-SATURATION{}: {:.2}s, answered {} unsat + {} sat of {} subjects ({} residue to probes, known-label-subjects={}, satcache={})",
                    if saturation_complete { "" } else { "-PARTIAL" },
                    t_sat.elapsed().as_secs_f64(),
                    answered_unsat,
                    answered_sat,
                    answered_unsat + answered_sat + pending.len(),
                    pending.len(),
                    outcome
                        .known_subsumers
                        .iter()
                        .filter(|subsumers| !subsumers.is_empty())
                        .count(),
                    satcache_active,
                );
            }
        }
    }
    if kpset_state.is_none() {
        let empty_verdict = vec![None; n_named];
        let empty_certain = vec![None; n_named];
        let mut known = vec![Vec::new(); n_named];
        for &(sub, sup) in &saturation_known_pairs {
            if sub < n_named && sup < n_named {
                known[sub].push(sup);
            }
        }
        let state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &empty_verdict,
            &empty_certain,
            &known,
            &pending,
            ctx.ontology_arenas().concepts(),
        );
        pending = state.ordered_subjects.clone();
        kpset_state = Some(state);
    }
    // Diagnostic split: retain Konclude's saturation-label replay/blocking but
    // suppress only the associated-expansion cache shared across completion
    // probes.  This distinguishes a bad raw saturation label from a bad
    // completion-cache write without disabling the whole saturation coupling.
    if satcache_active && std::env::var_os("KM_HT_NO_ASSOC_EXP_CACHE").is_none() {
        install_bridge_saturation_node_expansion_cache(&mut ctx);
    }
    if std::env::var_os("KM_HT_NO_SAT_EXP_CACHE").is_none() {
        install_bridge_satisfiable_expander_cache(&mut ctx);
    }
    let mut kpset_state = kpset_state.expect("synchronous KPSet state initialized");
    // Diagnostic scheduler replay: accept an explicit comma-separated subject
    // order so a Konclude trace can be replayed without baking ontology names or
    // ids into the reasoner. Production never sets these variables.
    if let Ok(order) = std::env::var("KM_BRIDGE_ORDER_SUBJECTS") {
        let ordered: Vec<usize> = order
            .split(',')
            .filter_map(|value| value.trim().parse().ok())
            .collect();
        let rank: HashMap<usize, usize> = ordered
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, subject)| (subject, rank))
            .collect();
        let original_rank: HashMap<usize, usize> = pending
            .iter()
            .copied()
            .enumerate()
            .map(|(rank, subject)| (subject, rank))
            .collect();
        pending.sort_by_key(|subject| {
            (
                rank.get(subject).copied().unwrap_or(usize::MAX),
                original_rank.get(subject).copied().unwrap_or(usize::MAX),
            )
        });
        if std::env::var_os("KM_BRIDGE_ORDER_ONLY").is_some() {
            pending.retain(|subject| rank.contains_key(subject));
        }
    }
    // Diagnostic only: retain a single post-saturation subject while preserving
    // construction of the complete KPSet graph and saturation cache above.
    if let Ok(subject) = std::env::var("KM_BRIDGE_ONLY_SUBJECT") {
        if let Ok(subject) = subject.parse::<usize>() {
            pending.retain(|&candidate| candidate == subject);
        }
    }
    let subject_by_item: HashMap<usize, usize> = kpset_state
        .item_ids
        .iter()
        .enumerate()
        .filter_map(|(subject, item)| item.is_some().then_some((item.index(), subject)))
        .collect();
    let subject_by_concept: HashMap<ConceptId, usize> = bridged
        .named
        .iter()
        .copied()
        .enumerate()
        .map(|(subject, concept)| (concept, subject))
        .collect();
    // Classify one subject end-to-end (read-off + any needed verification
    // probes) into `out`. `None` ⇔ some probe STOPped — the subject is
    // DEFERRED, `out` untouched for it (pairs are only pushed once every
    // probe of the subject has a verdict).
    // KM_BRIDGE_FRESH_ENV=1 (diagnostic): rebuild the env per probe instead
    // of resetting — the pre-#13 isolation, for A/B against the reset path.
    let fresh_env = std::env::var_os("KM_BRIDGE_FRESH_ENV").is_some();
    // KM_BRIDGE_COW_CONFIRM=1 (opt-in): re-run poison-deferred probes under
    // COW branch epochs to CONFIRM them instead of deferring. Correct
    // (complete restore ⇒ classically complete) but measured too slow inside
    // the probe budgets on the recognition family (the uniform first-touch
    // journal cost — ore_ont_12653 subjects blew their 900 s validation
    // window). Becomes the default once per-node COW localization lands.
    let cow_confirm = std::env::var_os("KM_BRIDGE_COW_CONFIRM").is_some();
    let mut synchronous_satisfiable_phase_finished = false;
    let mut classify_one = |s: usize,
                            algo: &mut CompletionTaskHandleAlgorithm,
                            ctx: &mut CalculationAlgorithmContextBase,
                            out: &mut BridgedClassification,
                            prepare_only: bool|
     -> Option<()> {
        // Konclude does not begin possible-subsumption calculations until
        // every satisfiability job has returned.  The first verification call
        // is the synchronous barrier: build the KPSet propagation graph and
        // prune the completed maps before looking at a single pair.
        if !prepare_only && !synchronous_satisfiable_phase_finished {
            classifier.finish_synchronous_satisfiable_phase(
                &mut kpset_state,
                ctx.ontology_arenas().concepts(),
            );
            synchronous_satisfiable_phase_finished = true;
        }
        let t_subj = std::time::Instant::now();
        let mut renew = |algo: &mut CompletionTaskHandleAlgorithm,
                         ctx: &mut CalculationAlgorithmContextBase,
                         cow: bool| {
            if fresh_env {
                let budget = algo.probe_budget;
                let (a2, c2, _b2) = fresh_bridge_env(tin);
                *algo = a2;
                *ctx = c2;
                algo.probe_budget = budget;
            } else {
                reset_probe_env(algo, ctx, &bridged, saturation_ran);
            }
            configure_production_search(algo);
            if ctx.base.used_sat_exp_cache_handler.is_some() {
                // CCalculationTableauCompletionTaskHandleAlgorithm defaults,
                // cpp 194-199 and readCalculationConfig cpp 536-539.
                algo.conf_sat_exp_cache_retrieval = true;
                algo.conf_sat_exp_cache_concept_expansion = true;
                algo.conf_sat_exp_cache_satisfiable_blocking = true;
                algo.conf_sat_exp_cache_writing = true;
            }
            // Saturation-node coupling (task #24 wave 2): Konclude's production
            // completion profile — expand created successors from saturation +
            // caching-blocking from saturation, including cache revalidation
            // after modification. Successful jobs also extend the shared
            // associated-expansion cache. Re-armed after every reset because
            // the reset rebuilds the algorithm. The KM_BRIDGE_FRESH_ENV
            // diagnostic path rebuilds an UNsaturated env, so the coupling
            // stays off there (the lookups would find no reference linkings).
            if satcache_active && !fresh_env {
                configure_production_completion_saturation_coupling(algo);
                algo.conf_saturation_satisfiabilitiy_expansion_cache_writing =
                    std::env::var_os("KM_HT_NO_SAT_CACHE_WRITING").is_none();
            }
            // VERDICT TRUST HIERARCHY, escalation leg: re-run an untrusted
            // probe under COW branch epochs — complete per-alternative state
            // restore, so chronological search is classically complete and
            // the unrestored-advance poison never fires. Slower (journaling)
            // — used only to CONFIRM a plain-mode verdict tainted by
            // phantomized nodes. Oracle-validated (plain/COW matrix).
            if cow {
                algo.conf_inprocess_cow = true;
            }
        };
        let derived = {
            let item = &kpset_state
                .ontology_item
                .get_concept_satisfiable_test_item_container()[kpset_state.item_ids[s].index()];
            if item.is_result_unsatisfiable_derivated() {
                out.unsatisfiable.push(s);
                return Some(());
            }
            item.is_result_satisfiable_derivated().then(|| {
                let mut candidates: Vec<usize> = item
                    .get_subsuming_concept_item_list()
                    .iter()
                    .filter_map(|known| subject_by_item.get(&known.index()).copied())
                    .collect();
                if let Some(possible) = item.get_possible_subsumption_map_ref() {
                    candidates.extend(
                        possible
                            .concepts()
                            .into_iter()
                            .filter_map(|concept| subject_by_concept.get(&concept).copied()),
                    );
                }
                candidates.sort_unstable();
                candidates.dedup();
                candidates
            })
        };
        let (mut subs, authoritative, root) = if let Some(subs) = derived {
            if progress {
                eprintln!(
                    "BRIDGE-KPSET-DERIVED subject {s}: {} candidates, no satisfiability job",
                    subs.len()
                );
            }
            (subs, false, None)
        } else {
            renew(algo, ctx, false);
            let mut next_indi_id: i64 = 1_000;
            let mut readoff = bridged_classify_subject_with_root(
                algo,
                ctx,
                &bridged,
                &mut next_indi_id,
                s,
                n_named,
            );
            if readoff.is_none() && algo.completeness_poisoned && cow_confirm {
                // Plain search untrusted (an unrestored advance phantomized
                // nodes) — the poison deferred the read-off. Escalate to COW.
                renew(algo, ctx, true);
                let mut id_cow: i64 = 1_000;
                readoff = bridged_classify_subject_with_root(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    s,
                    n_named,
                );
            }
            if readoff.is_none() && progress {
                eprintln!(
                    "BRIDGE-DEFER subject {s}: READ-OFF stop after {:.1}s (signal={:?}, nodes={}, sat-blocks={}, sat-expanded={})",
                    t_subj.elapsed().as_secs_f64(),
                    ctx.pending_signal(),
                    ctx.process_context().node_count(),
                    algo.saturation_cache_establish_count,
                    algo.saturation_expansion_concept_count,
                );
            }
            let (subs, authoritative, root) = readoff?;
            (subs, authoritative, Some(root))
        };
        if let Some(root) = root {
            if !(authoritative && subs.len() == n_named) {
                analyse_kpset_completion_model(&mut classifier, &mut kpset_state, s, root, ctx);
            }
        }
        if !authoritative {
            // Konclude does not restrict possible-subsumption tests to the
            // named concepts visible in the completion model's root label.
            // The satisfiability job emits
            // CClassificationInitializePossibleClassSubsumptionMessageData;
            // COptimizedKPSetClassSubsumptionClassifierThread.cpp
            // 1835-1904 installs that message's candidates in the possible
            // map, and lines 868-895 schedule every remaining entry after the
            // satisfiability phase. `analyse_kpset_completion_model` above is
            // the synchronous message delivery. Refresh `subs` from the map
            // after delivery so this synchronous driver executes the same
            // transition instead of testing only the pre-message read-off.
            let item = &kpset_state
                .ontology_item
                .get_concept_satisfiable_test_item_container()[kpset_state.item_ids[s].index()];
            subs.extend(
                item.get_subsuming_concept_item_list()
                    .iter()
                    .filter_map(|known| subject_by_item.get(&known.index()).copied()),
            );
            if let Some(possible) = item.get_possible_subsumption_map_ref() {
                subs.extend(
                    possible
                        .concepts()
                        .into_iter()
                        .filter_map(|concept| subject_by_concept.get(&concept).copied()),
                );
            }
            subs.sort_unstable();
            subs.dedup();
        }
        // Optional diagnostic filter: intersect a second model obtained with
        // reversed disjunction order. This is sound, but it is not part of
        // Konclude's KPSet pipeline. Konclude consumes the first model's
        // possible-subsumption/pseudo-model messages and verifies the remaining
        // pairs. On the disjunction family a second full read-off usually
        // removes only one candidate and costs far more than those pair checks.
        if !authoritative && std::env::var_os("KM_BRIDGE_REVERSE_READOFF").is_some() {
            renew(algo, ctx, false);
            algo.conf_or_reverse = true;
            let mut id_rev: i64 = 1_000;
            if let Some((subs_rev, _, reverse_root)) =
                bridged_classify_subject_with_root(algo, ctx, &bridged, &mut id_rev, s, n_named)
            {
                analyse_kpset_completion_model(
                    &mut classifier,
                    &mut kpset_state,
                    s,
                    reverse_root,
                    ctx,
                );
                if subs_rev.len() < n_named {
                    let keep: std::collections::HashSet<usize> = subs_rev.into_iter().collect();
                    let before = subs.len();
                    subs.retain(|c| keep.contains(c));
                    if progress && subs.len() != before {
                        let names: Vec<&str> = subs
                            .iter()
                            .take(48)
                            .map(|&c| tin.concepts[c].as_str())
                            .collect();
                        eprintln!(
                            "BRIDGE-INTERSECT subject {s} ({}): candidates {before} -> {} [{}]",
                            tin.concepts[s],
                            subs.len(),
                            names.join(",")
                        );
                    }
                }
            }
            algo.conf_or_reverse = false;
        }
        // The subject-unsatisfiable signal is the FULL index range
        // (authoritative). A tiny ontology can legitimately have a subject
        // subsumed by every named concept, so disambiguate with a direct
        // single-seed unsat probe.
        if authoritative && subs.len() == n_named {
            renew(algo, ctx, false);
            let mut id2: i64 = 1_000;
            let mut v = bridged_unsat(algo, ctx, &bridged, &mut id2, &[(bridged.named[s], false)]);
            if v.is_none() && algo.completeness_poisoned && cow_confirm {
                renew(algo, ctx, true);
                let mut id_cow: i64 = 1_000;
                v = bridged_unsat(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    &[(bridged.named[s], false)],
                );
            }
            match v {
                Some(true) => {
                    out.unsatisfiable.push(s);
                    return Some(());
                }
                Some(false) => {} // genuinely subsumed by everything — keep pairs
                None => return None,
            }
        }
        // Restrict candidates to the classification universe (real named
        // classes; see the `universe` doc above). AFTER the full-range unsat
        // disambiguation — that signal is defined on the raw read-off.
        subs.retain(|&c| c == s || universe.contains(&c));
        if authoritative {
            for c in subs {
                if c != s && !saturation_known_pairs.contains(&(s, c)) {
                    out.subsumptions.push((s, c));
                }
            }
            return Some(());
        }
        if prepare_only {
            // The completion-model analyser above has delivered Konclude's
            // deterministic-subsumer, possible-subsumer, and pseudo-model
            // messages into the persistent KPSet item.  Pair verification is
            // intentionally deferred until every subject reaches this point.
            return Some(());
        }
        // Non-deterministic subject: verify each candidate pairwise. Collect
        // locally and commit only when EVERY probe answered, so a deferred
        // subject leaves no partial pairs behind for the retry round.
        let mut pairs: Vec<(usize, usize)> = Vec::new();
        for c in subs {
            if c == s {
                continue;
            }
            if saturation_known_pairs.contains(&(s, c)) {
                continue;
            }
            if let Some((confirmed, invalid)) = kpset_state.candidate_state(s, c) {
                if invalid {
                    if progress {
                        eprintln!(
                            "BRIDGE-KPSET-SKIP {} v {}: propagated-false",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    continue;
                }
                if confirmed {
                    if progress {
                        eprintln!(
                            "BRIDGE-KPSET-SKIP {} v {}: propagated-true",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    pairs.push((s, c));
                    continue;
                }
            }
            if kpset_state.pseudo_model_refutes(s, c) {
                if progress {
                    eprintln!(
                        "BRIDGE-KPSET-SKIP {} v {}: pseudo-model-false",
                        tin.concepts[s], tin.concepts[c]
                    );
                }
                kpset_state
                    .ontology_item
                    .inc_running_possible_subsumption_tests_count(1);
                classifier.interprete_subsumption_result(
                    &mut kpset_state.ontology_item,
                    bridged.named[s],
                    bridged.named[c],
                    false,
                    ctx.ontology_arenas().concepts(),
                );
                continue;
            }
            if progress {
                eprintln!(
                    "BRIDGE-PAIR-START {} v {}",
                    tin.concepts[s], tin.concepts[c]
                );
            }
            renew(algo, ctx, false);
            let mut id2: i64 = 1_000;
            let mut v = bridged_unsat(
                algo,
                ctx,
                &bridged,
                &mut id2,
                &[(bridged.named[s], false), (bridged.named[c], true)],
            );
            if v.is_none() && algo.completeness_poisoned && cow_confirm {
                // plain verdict untrusted — confirm under COW epochs
                renew(algo, ctx, true);
                let mut id_cow: i64 = 1_000;
                v = bridged_unsat(
                    algo,
                    ctx,
                    &bridged,
                    &mut id_cow,
                    &[(bridged.named[s], false), (bridged.named[c], true)],
                );
            }
            match v {
                Some(true) => {
                    if progress {
                        eprintln!(
                            "BRIDGE-PAIR-END {} v {}: true",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    kpset_state
                        .ontology_item
                        .inc_running_possible_subsumption_tests_count(1);
                    classifier.interprete_subsumption_result(
                        &mut kpset_state.ontology_item,
                        bridged.named[s],
                        bridged.named[c],
                        true,
                        ctx.ontology_arenas().concepts(),
                    );
                    pairs.push((s, c))
                }
                Some(false) => {
                    if progress {
                        eprintln!(
                            "BRIDGE-PAIR-END {} v {}: false",
                            tin.concepts[s], tin.concepts[c]
                        );
                    }
                    kpset_state
                        .ontology_item
                        .inc_running_possible_subsumption_tests_count(1);
                    classifier.interprete_subsumption_result(
                        &mut kpset_state.ontology_item,
                        bridged.named[s],
                        bridged.named[c],
                        false,
                        ctx.ontology_arenas().concepts(),
                    );
                }
                None => {
                    if progress {
                        eprintln!(
                            "BRIDGE-DEFER subject {s}: PAIR {}v{} stop after {:.1}s subj-total",
                            tin.concepts[s],
                            tin.concepts[c],
                            t_subj.elapsed().as_secs_f64()
                        );
                    }
                    return None;
                }
            }
        }
        out.subsumptions.extend(pairs);
        // A non-deterministic subject can also be unsatisfiable without the
        // read-off reporting the full range (a clash IS reported full-range,
        // so this is only reachable when the drive found a model — the
        // subject is satisfiable; nothing to check).
        Some(())
    };
    // Phase 1: run every satisfiability-model job and deliver all of its
    // classification messages.  This is Konclude's satisfiability phase; no
    // possible-subsumption pair may be scheduled before its all-jobs barrier.
    let verification_subjects = pending.clone();
    let mut permanent_defer = 0usize;
    for round in 0..=retry_rounds {
        algo.probe_budget = Some(std::time::Duration::from_secs(
            base_budget.saturating_mul(4u64.saturating_pow(round)),
        ));
        let total = pending.len();
        let mut deferred: Vec<usize> = Vec::new();
        for (k, &s) in pending.iter().enumerate() {
            if classify_one(s, &mut algo, &mut ctx, &mut out, true).is_none() {
                if algo.completeness_poisoned {
                    permanent_defer += 1;
                } else {
                    deferred.push(s);
                }
            }
            log_bridge_satisfiable_expander_cache_stats(&ctx, "prepare", s);
            if progress && (k % 64 == 0 || k + 1 == total || permanent_defer > 0) {
                eprintln!(
                    "BRIDGE-PREPARE round {round} subject {}/{total} deferred={} permanent={}",
                    k + 1,
                    deferred.len(),
                    permanent_defer
                );
            }
            if permanent_defer > 0 {
                // One deterministic defer decides the whole classification
                // (complete-or-defer contract) — finishing the remaining
                // subjects is pure waste, and in the race the bridge worker
                // shares the node with the CB engine.
                break;
            }
        }
        pending = deferred;
        if pending.is_empty() || permanent_defer > 0 {
            break;
        }
    }
    if !pending.is_empty() || permanent_defer > 0 {
        if progress {
            eprintln!(
                "BRIDGE-PREPARE defer: {} budget + {} permanent subjects without a model",
                pending.len(),
                permanent_defer
            );
        }
        return None;
    }

    // Phase 2: the first call crosses the all-models barrier inside
    // `classify_one`, ports Konclude's global KPSet graph/map pruning, and
    // then verifies only candidates that remain unknown.  Successful model
    // jobs marked their items derived, so they are not rerun here.
    pending = verification_subjects;
    permanent_defer = 0;
    for round in 0..=retry_rounds {
        algo.probe_budget = Some(std::time::Duration::from_secs(
            base_budget.saturating_mul(4u64.saturating_pow(round)),
        ));
        let total = pending.len();
        let mut deferred: Vec<usize> = Vec::new();
        for (k, &s) in pending.iter().enumerate() {
            if classify_one(s, &mut algo, &mut ctx, &mut out, false).is_none() {
                if algo.completeness_poisoned {
                    permanent_defer += 1;
                } else {
                    deferred.push(s);
                }
            }
            log_bridge_satisfiable_expander_cache_stats(&ctx, "verify", s);
            if progress && (k % 64 == 0 || k + 1 == total || permanent_defer > 0) {
                eprintln!(
                    "BRIDGE-VERIFY round {round} subject {}/{total} deferred={} permanent={}",
                    k + 1,
                    deferred.len(),
                    permanent_defer
                );
            }
            if permanent_defer > 0 {
                break;
            }
        }
        pending = deferred;
        if pending.is_empty() || permanent_defer > 0 {
            break;
        }
    }
    // KM_HT_UNSATCACHE diagnostics: writes vs hits across the WHOLE
    // classification (the handler is carried across probe resets, so these
    // are cumulative). Interprets a null A/B result: 0 writes = the u22
    // guards rejected every candidate line; writes>0 hits=0 = the read
    // points never matched (label shapes / caching-tag mismatch).
    if progress {
        if let Some(state) = ctx.base.take_used_unsatisfiable_cache_handler() {
            eprintln!(
                "BRIDGE-CLASSIFY unsatcache: {} lines written, {} read hits",
                state.handler.stat_write_count, state.handler.stat_hit_count
            );
            ctx.base.restore_used_unsatisfiable_cache_handler(state);
        }
    }
    if !pending.is_empty() || permanent_defer > 0 {
        if progress {
            eprintln!(
                "BRIDGE-CLASSIFY defer: {} budget + {} permanent subjects without verdict",
                pending.len(),
                permanent_defer
            );
        }
        return None;
    }
    out.unsatisfiable.sort_unstable();
    out.unsatisfiable.dedup();
    if !out.unsatisfiable.is_empty() {
        let unsatisfiable: std::collections::HashSet<usize> =
            out.unsatisfiable.iter().copied().collect();
        out.subsumptions
            .retain(|(subject, _)| !unsatisfiable.contains(subject));
    }
    out.subsumptions.sort_unstable();
    out.subsumptions.dedup();
    Some(out)
}

// ---------------------------------------------------------------------------
// Tests: ofn text → frontend → cb_to_ht::convert → bridge → verdicts.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::super::completion::strategy::ConceptProcessingPriorityStrategy;
    use super::super::process::sat_node::IndividualSaturationProcessNode;
    use super::super::process::sat_ref::ExtendedConceptReferenceLinkingData;
    use super::*;

    fn trigger_test_roles(b: &mut Builder) -> (RoleId, RoleId, HashMap<RoleId, RoleId>) {
        let role = b.ctx.ontology_arenas_mut().alloc_role(Role::new());
        let mut inverse_obj = Role::new();
        inverse_obj.set_inverse_role(role);
        let inverse = b.ctx.ontology_arenas_mut().alloc_role(inverse_obj);
        b.ctx
            .ontology_arenas_mut()
            .role_mut(role)
            .set_inverse_role(inverse);
        let map = HashMap::from([(role, inverse), (inverse, role)]);
        (role, inverse, map)
    }

    #[test]
    fn saturation_extractor_reports_only_valid_intermediate_substitute_concepts() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let queried = b.atom(TAG_BASE + 1);
        let reported = b.atom(TAG_BASE + 2);
        let negated = b.atom(TAG_BASE + 3);
        let role_range = b.atom(TAG_BASE + 4);
        let range_role = b.ctx.ontology_arenas_mut().alloc_role(Role::new());
        drop(b);

        let make_node = |ctx: &mut CalculationAlgorithmContextBase,
                         individual_id: Cint64,
                         concept: ConceptId,
                         negation: bool,
                         role: RoleId| {
            let mut item = ExtendedConceptReferenceLinkingData::new();
            item.init_concept_saturation_testing_item(concept, negation, role);
            let item = ctx
                .process_context_mut()
                .alloc_extended_con_ref_linking_data(item);
            let node = ctx
                .process_context_mut()
                .alloc_sat_node(IndividualSaturationProcessNode::new(INVALID));
            ctx.process_context_mut()
                .sat_node_mut(node)
                .init_individual_saturation_process_node(individual_id, item, Id::NONE);
            node
        };

        // Konclude excludes the base node and the queried concept even when it
        // appears again on an intermediate substitute node.
        let base = make_node(&mut ctx, 1, reported, false, RoleId::NONE);
        let queried_again = make_node(&mut ctx, 2, queried, false, RoleId::NONE);
        let positive = make_node(&mut ctx, 3, reported, false, RoleId::NONE);
        let negative = make_node(&mut ctx, 4, negated, true, RoleId::NONE);
        let ranged = make_node(&mut ctx, 5, role_range, false, range_role);
        let terminal = make_node(&mut ctx, 6, role_range, false, RoleId::NONE);
        for (from, to) in [
            (base, queried_again),
            (queried_again, positive),
            (positive, negative),
            (negative, ranged),
            (ranged, terminal),
        ] {
            ctx.process_context_mut()
                .sat_node_mut(from)
                .set_substitute_individual_node(to);
        }

        let named_index = HashMap::from([
            (queried, 0usize),
            (reported, 1usize),
            (negated, 2usize),
            (role_range, 3usize),
        ]);
        let mut subsumers = Vec::new();
        let resolved =
            resolve_saturation_substitute_chain(&ctx, base, queried, &named_index, &mut subsumers);

        assert_eq!(resolved, terminal);
        assert_eq!(subsumers, vec![1]);
    }

    #[test]
    fn binary_absorber_combines_triggers_like_konclude() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let left = b.atom(TAG_BASE + 1);
        let right = b.atom(TAG_BASE + 2);
        let mut caches = TriggerCaches::default();
        let combined = combine_absorption_triggers(
            &mut b,
            vec![
                AbsorptionTrigger {
                    concept: left,
                    complexity: 1,
                },
                AbsorptionTrigger {
                    concept: right,
                    complexity: 1,
                },
            ],
            &mut caches,
        )
        .expect("binary trigger");
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(combined.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
        // Equal-complexity triggers follow CConceptTriggerLinker's decreasing
        // pointer order; the later arena id is the implication host.
        let right_concept = b.ctx.ontology_arenas().concept(right);
        assert_eq!(right_concept.get_operator_code(), op::CCSUB);
        let implication = right_concept.get_operand_list()[0].target;
        let implication_concept = b.ctx.ontology_arenas().concept(implication);
        assert_eq!(implication_concept.get_operator_code(), op::CCIMPL);
        assert_eq!(
            implication_concept.get_operand_list()[0].target,
            combined.concept
        );
        assert_eq!(implication_concept.get_operand_list()[1].target, left);
        assert!(implication_concept.get_operand_list()[1].negated);
    }

    #[test]
    fn existential_trigger_uses_inverse_implall_propagation() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let filler = b.atom(TAG_BASE + 1);
        let (role, inverse, inverses) = trigger_test_roles(&mut b);
        let some = b.some(role, (filler, false));
        let trigger = full_absorption_trigger(
            &mut b,
            (some, false),
            &inverses,
            &mut TriggerCaches::default(),
        )
        .expect("existential trigger");
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(trigger.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
        let filler_concept = b.ctx.ontology_arenas().concept(filler);
        assert_eq!(filler_concept.get_operator_code(), op::CCSUB);
        let propagation = filler_concept.get_operand_list()[0].target;
        let propagation_concept = b.ctx.ontology_arenas().concept(propagation);
        assert_eq!(propagation_concept.get_operator_code(), op::CCIMPLALL);
        assert_eq!(propagation_concept.get_role(), inverse);
        assert_eq!(
            propagation_concept.get_operand_list()[0].target,
            trigger.concept
        );
    }

    #[test]
    fn full_gci_keeps_named_condition_on_final_implication() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let named_condition = b.atom(TAG_BASE + 1);
        let filler = b.atom(TAG_BASE + 2);
        let implied = b.atom(TAG_BASE + 3);
        let (role, _, inverses) = trigger_test_roles(&mut b);
        let existential = b.some(role, (filler, false));
        let conjunction = b.and_of(&[(named_condition, false), (existential, false)]);
        assert!(absorb_concept_disjunction(
            &mut b,
            &[conjunction],
            &[(implied, false)],
            &inverses,
            &mut TriggerCaches::default(),
        ));

        let filler_unfolding = b.ctx.ontology_arenas().concept(filler).get_operand_list()[0].target;
        let structural_trigger = b
            .ctx
            .ontology_arenas()
            .concept(filler_unfolding)
            .get_operand_list()[0]
            .target;
        let binary_implication = b
            .ctx
            .ontology_arenas()
            .concept(structural_trigger)
            .get_operand_list()[0]
            .target;
        let binary = b.ctx.ontology_arenas().concept(binary_implication);
        assert_eq!(binary.get_operator_code(), op::CCIMPL);
        assert_eq!(binary.get_operand_count(), 2);
        let combined_trigger = binary.get_operand_list()[0].target;
        assert_eq!(binary.get_operand_list()[1].target, named_condition);
        assert!(binary.get_operand_list()[1].negated);
        let combined = b.ctx.ontology_arenas().concept(combined_trigger);
        assert_eq!(combined.get_operator_code(), op::CCIMPLTRIG);
        assert_eq!(combined.get_operand_list()[0].target, implied);
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(named_condition)
                .get_operand_count(),
            0,
            "the weaker named condition must not host the implication"
        );
    }

    #[test]
    fn full_or_trigger_uses_konclude_rounded_average_complexity() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let atom = b.atom(TAG_BASE + 1);
        let filler = b.atom(TAG_BASE + 2);
        let (role, _, inverses) = trigger_test_roles(&mut b);
        let exists = b.some(role, (filler, false));
        let disjunction = b.or_of(&[(atom, false), (exists, false)]);
        let trigger = full_absorption_trigger(
            &mut b,
            disjunction,
            &inverses,
            &mut TriggerCaches::default(),
        )
        .expect("fully absorbable disjunction");
        assert_eq!(trigger.complexity, 2, "Konclude computes (1 + 2 + 1) / 2");
    }

    #[test]
    fn ore_3215_common_condition_does_not_host_reverse_definitions() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let common = b.atom(TAG_BASE + 1);
        let alternative = b.atom(TAG_BASE + 2);
        let filler = b.atom(TAG_BASE + 3);
        let implied = b.atom(TAG_BASE + 4);
        let (role, _, inverses) = trigger_test_roles(&mut b);
        let exists = b.some(role, (filler, false));
        let disjunction = b.or_of(&[(alternative, false), (exists, false)]);
        let definition = b.and_of(&[(common, false), disjunction]);
        assert!(absorb_concept_disjunction(
            &mut b,
            &[definition],
            &[(implied, false)],
            &inverses,
            &mut TriggerCaches::default(),
        ));
        assert_eq!(
            b.ctx.ontology_arenas().concept(common).get_operand_count(),
            0,
            "the stronger rounded-average OR trigger must host the binary chain"
        );
    }

    #[test]
    fn branch_trigger_preprocess_installs_role_domain_marker() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let filler = b.atom(TAG_BASE + 1);
        let alternative = b.atom(TAG_BASE + 2);
        let (role, _, _) = trigger_test_roles(&mut b);
        let all = b.all(role, (filler, false));
        b.or_of(&[(all, false), (alternative, false)]);

        let count = install_branch_role_domain_triggers(&mut b, &mut TriggerCaches::default());
        assert_eq!(count, 1);
        let marker = b.ctx.ontology_arenas().role(role).domain_linker[0].target;
        let marker = b.ctx.ontology_arenas().concept(marker);
        assert_eq!(marker.get_operator_code(), op::CCIMPLTRIG);
        assert_eq!(marker.get_operand_count(), 0);
    }

    #[test]
    fn higher_cardinality_uses_partial_not_full_trigger() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let filler = b.atom(TAG_BASE + 1);
        let (role, inverse, inverses) = trigger_test_roles(&mut b);
        let atmost = b.atmost_q(role, 2, (filler, false));
        let mut caches = TriggerCaches::default();
        assert!(full_absorption_trigger(&mut b, (atmost, true), &inverses, &mut caches).is_none());
        let trigger = partial_absorption_trigger(&mut b, (atmost, true), &inverses, &mut caches)
            .expect("partial cardinality trigger");
        let filler_concept = b.ctx.ontology_arenas().concept(filler);
        let propagation = filler_concept.get_operand_list()[0].target;
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(propagation)
                .get_operator_code(),
            op::CCIMPLALL
        );
        assert_eq!(
            b.ctx.ontology_arenas().concept(propagation).get_role(),
            inverse
        );
        assert_eq!(
            b.ctx
                .ontology_arenas()
                .concept(trigger.concept)
                .get_operator_code(),
            op::CCIMPLTRIG
        );
    }

    #[test]
    fn common_disjunct_preprocess_materializes_replacement_data() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let common = b.atom(TAG_BASE + 1);
        let left_only = b.atom(TAG_BASE + 2);
        let right_only = b.atom(TAG_BASE + 3);
        let left = b.and_of(&[(common, false), (left_only, false)]);
        let right = b.and_of(&[(common, false), (right_only, false)]);
        let disjunction = b.or_of(&[left, right]).0;
        drop(b);

        assert!(extract_common_disjunct_replacements(&mut ctx) >= 1);
        let process_data = Id::new(
            ctx.ontology_arenas()
                .concept(disjunction)
                .get_concept_data(),
        );
        let replacement = ctx
            .ontology_arenas()
            .concept_process_data(process_data)
            .get_replacement_data();
        assert!(replacement.is_some());
        assert!(ctx
            .ontology_arenas()
            .replacement_data(replacement)
            .common_disjunct_concepts
            .iter()
            .any(|link| link.target == common && !link.negated));
    }

    #[test]
    fn common_disjunct_preprocess_reuses_nested_disjunction_cache_exactly() {
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut b = Builder {
            ctx: &mut ctx,
            next_tag: TAG_BASE,
        };
        let common = b.atom(TAG_BASE + 1);
        let left_only = b.atom(TAG_BASE + 2);
        let right_only = b.atom(TAG_BASE + 3);
        let outer_only = b.atom(TAG_BASE + 4);
        let left = b.and_of(&[(common, false), (left_only, false)]);
        let right = b.and_of(&[(common, false), (right_only, false)]);
        let shared = b.or_of(&[left, right]);
        let outer_right = b.and_of(&[(common, false), (outer_only, false)]);
        let outer = b.or_of(&[shared, outer_right]).0;
        let shared = shared.0;
        drop(b);

        assert!(extract_common_disjunct_replacements(&mut ctx) >= 2);
        for disjunction in [shared, outer] {
            let process_data = Id::new(
                ctx.ontology_arenas()
                    .concept(disjunction)
                    .get_concept_data(),
            );
            let replacement = ctx
                .ontology_arenas()
                .concept_process_data(process_data)
                .get_replacement_data();
            assert!(replacement.is_some());
            let common_links = &ctx
                .ontology_arenas()
                .replacement_data(replacement)
                .common_disjunct_concepts;
            assert!(
                common_links
                    .iter()
                    .any(|link| link.target == common && !link.negated),
                "shared and cached outer disjunction both retain the common concept"
            );
        }
    }

    struct BridgeEnv {
        tin: crate::orchestrate::cb_to_ht::TInput,
        con_id: std::collections::HashMap<String, usize>,
        // populated by the most recent probe (kept for diagnostics)
        ctx: Option<CalculationAlgorithmContextBase>,
        unsupported: usize,
    }

    /// Same as [`bridge_ofn`] but reads the ontology from a file path.
    fn bridge_ofn_path(path: &str) -> BridgeEnv {
        let text = std::fs::read_to_string(path).expect("readable ontology");
        bridge_ofn(&text)
    }

    /// ofn → clauses → TInput (the future production route input).
    fn bridge_ofn(text: &str) -> BridgeEnv {
        let fr = crate::frontend::ofn_to_clauses(text).expect("in fragment");
        let named: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let con_id = tin
            .concepts
            .iter()
            .enumerate()
            .map(|(i, n)| (n.clone(), i))
            .collect();
        BridgeEnv {
            tin,
            con_id,
            ctx: None,
            unsupported: 0,
        }
    }

    #[test]
    fn production_rbox_compiles_symmetric_role_as_self_inverse() {
        let env = bridge_ofn(
            "Prefix(:=<http://example.org/>)\n\
             Ontology(\n\
               Declaration(ObjectProperty(:r))\n\
               SymmetricObjectProperty(:r)\n\
             )",
        );
        assert!(env.tin.fenced.is_empty());
        assert!(env.tin.inverse);
    }

    #[test]
    fn production_rbox_marks_functional_role_for_successor_extension() {
        let env = bridge_ofn(
            "Prefix(:=<http://example.org/>)\n\
             Ontology(\n\
               Declaration(ObjectProperty(:r))\n\
               FunctionalObjectProperty(:r)\n\
             )",
        );
        let (_, ctx, bridged) = fresh_bridge_env(&env.tin);
        assert!(ctx.ontology_arenas().role(bridged.roles[0]).is_functional());
    }

    #[test]
    fn saturation_construction_ports_special_reference_and_exist_flags() {
        use super::super::model::concept_process::SATURATION_SUBSTITUTE_MODE;

        let env = bridge_ofn(
            "Prefix(:=<http://example.org/>)\n\
             Ontology(\n\
               Declaration(Class(:A)) Declaration(Class(:B))\n\
               Declaration(Class(:C)) Declaration(Class(:X))\n\
               Declaration(ObjectProperty(:r))\n\
               SubClassOf(:A :B)\n\
               SubClassOf(:X ObjectSomeValuesFrom(:r :C))\n\
             )",
        );
        let (_algo, mut ctx, mut bridged) = fresh_bridge_env(&env.tin);
        let a = bridged.named[env.con_id["A"]];
        let b = bridged.named[env.con_id["B"]];
        let c = bridged.named[env.con_id["C"]];
        let x = bridged.named[env.con_id["X"]];
        let r = bridged.roles[0];
        let next_tag = (0..ctx.ontology_arenas().concept_count())
            .map(|index| {
                ctx.ontology_arenas()
                    .concept(ConceptId::new(index))
                    .get_concept_tag()
            })
            .max()
            .unwrap_or(TAG_BASE)
            + 1;
        let (some, disjunction) = {
            let mut builder = Builder {
                ctx: &mut ctx,
                next_tag,
            };
            let some = builder.some(r, (c, false));
            let disjunction = builder.or_of(&[(a, false), (c, false)]).0;
            (some, disjunction)
        };
        // A is also a positive named disjunct. Konclude keeps A's ordinary
        // A -> B special reference in this case.
        bridged.tbox.push(disjunction);
        ctx.ontology_arenas_mut()
            .concept_mut(a)
            .set_operator_code(op::CCSUB)
            .set_operand_list(vec![super::super::model::NegLink {
                target: b,
                negated: false,
            }])
            .set_operand_count(1);
        ctx.ontology_arenas_mut()
            .concept_mut(x)
            .set_operator_code(op::CCSUB)
            .set_operand_list(vec![super::super::model::NegLink {
                target: some,
                negated: false,
            }])
            .set_operand_count(1);
        build_saturation_seeds(&mut ctx, &bridged);

        let item_for = |name: &str, ctx: &CalculationAlgorithmContextBase| {
            let named_index = env.con_id[name];
            let concept = bridged.named[named_index];
            let process_data = super::super::model::concept_process::ConceptProcessDataId::new(
                ctx.ontology_arenas().concept(concept).get_concept_data(),
            );
            let reference_data = ctx
                .ontology_arenas()
                .concept_process_data(process_data)
                .get_concept_reference_linking();
            ctx.ontology_arenas()
                .concept_saturation_reference_linking_data(reference_data)
                .get_concept_saturation_reference_linking_data(false)
        };
        let a_item = item_for("A", &ctx);
        let b_item = item_for("B", &ctx);
        let c_item = item_for("C", &ctx);
        let a_data = ctx
            .ontology_arenas()
            .saturation_concept_reference_linking(a_item);
        assert_eq!(a_data.get_special_item_reference(), b_item);
        assert_eq!(
            a_data.get_special_reference_mode(),
            SATURATION_SUBSTITUTE_MODE
        );
        let a_node = a_data.get_individual_process_node_for_concept();
        let b_node = ctx
            .ontology_arenas()
            .saturation_concept_reference_linking(b_item)
            .get_individual_process_node_for_concept();
        assert!(
            ctx.process_context().sat_node(b_node).get_individual_id()
                > ctx.process_context().sat_node(a_node).get_individual_id(),
            "Konclude's reversed construction list gives dependencies higher priority IDs"
        );
        assert!(!a_data.is_potentially_exist_initialization_concept());
        assert!(ctx
            .ontology_arenas()
            .saturation_concept_reference_linking(c_item)
            .is_potentially_exist_initialization_concept());
    }

    impl BridgeEnv {
        /// One probe = one fresh context + bridged terminology. Per-probe
        /// isolation: an UNSAT probe leaves clash-laden nodes + queued work
        /// behind, which would leak spurious clashes into the next probe.
        /// Konclude isolates probes via per-task databox COW (the unported
        /// Task layer); the v1 driver rebuilds instead — same verdicts,
        /// O(TBox) per probe.
        fn subsumes(&mut self, sub: &str, sup: &str) -> bool {
            self.try_subsumes(sub, sup)
                .unwrap_or_else(|| panic!("probe {sub} ⊑ {sup} raised STOP (undecided)"))
        }

        /// Like [`Self::subsumes`] but surfaces STOP/DEFER as `None` instead
        /// of panicking — for tests asserting "must not answer WRONG"
        /// (a defer is acceptable, a wrong verdict is not).
        fn try_subsumes(&mut self, sub: &str, sup: &str) -> Option<bool> {
            let mut algo = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo);
            let mut ctx = CalculationAlgorithmContextBase::new();
            ctx.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx.ontology_arenas_mut().alloc_concept(c)
            };
            ctx.processing_data_box_mut().ontology_top_concept = top;
            let bridged = bridge_tinput(&mut ctx, &self.tin);
            algo.singleton_concepts = bridged.singleton_concepts.clone();
            self.unsupported = bridged.unsupported;
            let idx = |s: &str| -> usize {
                *self
                    .con_id
                    .get(s)
                    .unwrap_or_else(|| panic!("concept {s} not in TInput"))
            };
            let a = bridged.named[idx(sub)];
            let b = bridged.named[idx(sup)];
            let mut next_indi_id = 0i64;
            let r = bridged_unsat(
                &mut algo,
                &mut ctx,
                &bridged,
                &mut next_indi_id,
                &[(a, false), (b, true)],
            );
            self.ctx = Some(ctx);
            r
        }
    }

    const PREFIX: &str = "Prefix(:=<http://km.test/>)\nOntology(<http://km.test/o>\n";

    #[test]
    fn bridge_subsumption_chain() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             SubClassOf(:A :B)\n\
             SubClassOf(:B :C)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(env.subsumes("A", "B"), "A ⊑ B (direct)");
        assert_eq!(env.unsupported, 0, "chain TBox fully bridged");
        assert!(env.subsumes("A", "C"), "A ⊑ C (chained)");
        assert!(!env.subsumes("C", "A"), "C ⊑ A must NOT hold");
    }

    #[test]
    fn source_absorber_registers_unabsorbed_equivalent_non_candidate() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:H)) Declaration(Class(:M)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             EquivalentClasses(:H ObjectIntersectionOf(\
                 :M ObjectAllValuesFrom(:r :C)))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // `ofn_to_clauses` emits this side channel only when the production
        // environment enables trigger absorption. Supply the normalized axiom
        // directly so this unit test is independent of process-global env vars.
        env.tin.source_axioms = vec![crate::json_io::SourceAxiomMeta {
            kind: crate::json_io::SourceAxiomKind::Equivalent,
            left: SourceConcept::Name("H".into()),
            right: SourceConcept::And(std::collections::BTreeSet::from([
                SourceConcept::Name("M".into()),
                SourceConcept::Forall(
                    SourceRole::Name("r".into()),
                    Box::new(SourceConcept::Name("C".into())),
                ),
            ])),
        }];
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;

        let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, &env.tin, true);
        let host = bridged.named[*env.con_id.get("H").expect("H in TInput")];
        assert_eq!(
            ctx.ontology_arenas().concept(host).get_operator_code(),
            op::CCEQ,
            "the positive universal prevents full equivalence absorption"
        );
        assert!(
            ctx.ontology_arenas()
                .get_equivalent_concept_non_candidate_set()
                .expect("absorber creates Konclude's TBox set")
                .contains(&host),
            "the retained CCEQ host remains a classification possible-subsumer"
        );
    }

    #[test]
    fn source_tbox_retains_rbox_domain_for_existential_saturation() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |cc: usize, t: usize| HAtom::Concept {
            neg: false,
            c: cc,
            t,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "D".into(), "T".into(), "X".into()],
            roles: vec!["r".into()],
            clauses: vec![
                // Clausified copy of the source axiom. Source mode suppresses
                // this because the native source concept below replaces it.
                HtClause {
                    body: vec![c(0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 2,
                        t: 0,
                    }],
                },
                // Simple ObjectPropertyDomain(r D), emitted outside the source
                // class-axiom side channel and retained as a CRole linker.
                HtClause {
                    body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                    head: vec![c(1, 0)],
                },
                // The same guarded shape can be generated from an ordinary
                // class axiom. It is not a native role domain without RBox
                // provenance and must stay suppressed in source mode.
                HtClause {
                    body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                    head: vec![c(3, 0)],
                },
            ],
            role_domains: vec![(0, 1)],
            source_axioms: vec![crate::json_io::SourceAxiomMeta {
                kind: crate::json_io::SourceAxiomKind::SubClass,
                left: SourceConcept::Name("A".into()),
                right: SourceConcept::Exists(
                    SourceRole::Name("r".into()),
                    Box::new(SourceConcept::Name("T".into())),
                ),
            }],
            ..Default::default()
        };

        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;

        let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, &tin, true);
        assert!(bridged.source_tbox);
        assert_eq!(bridged.unsupported, 0);
        assert!(
            ctx.ontology_arenas()
                .role(bridged.roles[0])
                .get_domain_concept_list()
                .iter()
                .any(|link| link.target == bridged.named[1] && !link.negated),
            "source mode must install D on r's native domain linker"
        );
        assert!(
            !ctx.ontology_arenas()
                .role(bridged.roles[0])
                .get_domain_concept_list()
                .iter()
                .any(|link| link.target == bridged.named[3]),
            "guarded clause shape alone must not manufacture a native domain"
        );

        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let out = extract_saturation_outcome(&mut ctx, &bridged);
        assert_eq!(out.sat_verdict[0], Some(false));
        assert!(
            out.certain_subsumers[0]
                .as_ref()
                .is_some_and(|subsumers| subsumers.contains(&1)),
            "A ⊆ ∃r.T and Domain(r,D) must saturate A ⊆ D"
        );
        assert!(
            !out.known_subsumers[0].contains(&3),
            "the non-RBox guarded clause must not saturate A ⊆ X"
        );
    }

    #[test]
    fn source_tbox_propagates_complex_role_domain_back_through_chain() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |cc: usize, t: usize| HAtom::Concept {
            neg: false,
            c: cc,
            t,
        };
        let exists = |body: usize, role: usize, filler: usize| HtClause {
            body: vec![c(body, 0)],
            head: vec![HAtom::Exist {
                r: role,
                neg: false,
                c: filler,
                t: 0,
            }],
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into(), "D".into()],
            roles: vec!["r".into(), "s".into(), "t".into()],
            clauses: vec![
                // Clausified copies are suppressed in source mode.
                exists(0, 0, 1),
                exists(1, 1, 2),
                // ObjectPropertyDomain(t D) remains a native CRole linker.
                HtClause {
                    body: vec![HAtom::Role { r: 2, s: 0, t: 1 }],
                    head: vec![c(3, 0)],
                },
            ],
            chains: vec![(0, 1, 2)],
            role_domains: vec![(2, 3)],
            source_axioms: vec![
                crate::json_io::SourceAxiomMeta {
                    kind: crate::json_io::SourceAxiomKind::SubClass,
                    left: SourceConcept::Name("A".into()),
                    right: SourceConcept::Exists(
                        SourceRole::Name("r".into()),
                        Box::new(SourceConcept::Name("B".into())),
                    ),
                },
                crate::json_io::SourceAxiomMeta {
                    kind: crate::json_io::SourceAxiomKind::SubClass,
                    left: SourceConcept::Name("B".into()),
                    right: SourceConcept::Exists(
                        SourceRole::Name("s".into()),
                        Box::new(SourceConcept::Name("C".into())),
                    ),
                },
            ],
            ..Default::default()
        };

        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;

        let bridged = bridge_tinput_with_trigger_absorption(&mut ctx, &tin, true);
        assert!(bridged.source_tbox);
        assert_eq!(bridged.unsupported, 0);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        let out = extract_saturation_outcome(&mut ctx, &bridged);
        assert_eq!(out.sat_verdict[0], Some(false));
        assert!(
            out.certain_subsumers[0]
                .as_ref()
                .is_some_and(|subsumers| subsumers.contains(&3)),
            "A ⊑ ∃r.B, B ⊑ ∃s.C, r∘s ⊑ t, Domain(t,D) must saturate A ⊑ D"
        );
    }

    #[test]
    fn bridge_materializes_transitive_role_for_automata_preprocessing() {
        let mut tin = TInput {
            concepts: vec!["A".to_string()],
            roles: vec!["r".to_string()],
            ..TInput::default()
        };
        let role_index = 0;
        tin.transitive.push(role_index);
        let mut ctx = CalculationAlgorithmContextBase::new();
        let mut top = Concept::new();
        top.set_concept_tag(1);
        top.set_operator_code(op::CCTOP);
        let top = ctx.ontology_arenas_mut().alloc_concept(top);
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &tin);
        assert_eq!(bridged.unsupported, 0);
        assert_eq!(ctx.ontology_arenas().role_chain_count(), 2);
        assert!(ctx
            .ontology_arenas()
            .role(bridged.roles[role_index])
            .is_complex_role());
        let role = ctx.ontology_arenas().role(bridged.roles[role_index]);
        assert!(role
            .get_indirect_super_role_list()
            .iter()
            .any(|link| link.target == bridged.roles[role_index] && !link.negated));
        assert_eq!(role.get_role_chain_super_sharing_linker().len(), 1);
        assert!(ctx
            .ontology_arenas()
            .role(role.get_inverse_role())
            .is_complex_role());
    }

    #[test]
    fn structural_markers_are_not_classification_or_saturation_items() {
        let tin = TInput {
            concepts: vec!["A".to_string(), "Q_1".to_string()],
            queries: vec![0],
            ..TInput::default()
        };
        let (_algo, mut ctx, bridged) = fresh_bridge_env(&tin);
        assert!(ctx
            .ontology_arenas()
            .concept(bridged.named[0])
            .has_class_name());
        assert!(!ctx
            .ontology_arenas()
            .concept(bridged.named[1])
            .has_class_name());

        build_saturation_seeds(&mut ctx, &bridged);
        assert!(super::super::saturation::algorithm::SaturationTaskHandleAlgorithm::s07_concept_reference_node(
            bridged.named[0],
            false,
            &mut ctx,
        )
        .is_some());
        assert!(super::super::saturation::algorithm::SaturationTaskHandleAlgorithm::s07_concept_reference_node(
            bridged.named[1],
            false,
            &mut ctx,
        )
        .is_none());

        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &[None, None],
            &[None, None],
            &[Vec::new(), Vec::new()],
            &[0],
            ctx.ontology_arenas().concepts(),
        );
        assert!(state.item_ids[0].is_some());
        assert!(state.item_ids[1].is_none());
        assert_eq!(state.ordered_subjects, vec![0]);
    }

    #[test]
    fn production_role_automata_solves_mini7914_unsat() {
        let mut env = bridge_ofn(include_str!(
            "../../../tests/completeness-gaps/mini7914_unsat.ofn"
        ));
        let hp = env
            .tin
            .roles
            .iter()
            .position(|role| role.rsplit(['#', '/']).next() == Some("hp"))
            .expect("hp in mini7914 role signature");
        assert!(
            env.tin.transitive.contains(&hp),
            "the frontend must retain Functional Syntax transitivity"
        );
        let x = *env.con_id.get("X").expect("X in mini7914 signature");
        let completion = bridged_classify_opts(&env.tin, false, false)
            .expect("mini7914 completion must classify without deferring");
        assert!(
            completion.unsatisfiable.contains(&x),
            "production role automata must make X unsatisfiable in completion"
        );
        let result = bridged_classify_opts(&env.tin, true, true)
            .expect("mini7914 must classify without deferring");
        assert!(
            result.unsatisfiable.contains(&x),
            "common consequences of both disjuncts must make X unsatisfiable"
        );
        assert!(
            result.subsumptions.iter().all(|(subject, _)| *subject != x),
            "unsatisfiable subjects are represented by #UNSAT, not redundant pairs"
        );
    }

    #[test]
    fn production_inverse_chain_automata_solves_7914_recognition_core() {
        let mut env = bridge_ofn(include_str!(
            "../../../tests/completeness-gaps/mini7914_chain_recognition.ofn"
        ));
        let r = env
            .tin
            .roles
            .iter()
            .position(|role| role.rsplit(['#', '/']).next() == Some("r"))
            .expect("r in recognition-core role signature");
        assert!(env.tin.transitive.contains(&r));
        assert_eq!(env.tin.chains.len(), 2);
        assert!(
            env.subsumes("X", "Target"),
            "inverse-trigger recognition must traverse forward and inverse chains"
        );
        let x = env.con_id["X"];
        let target = env.con_id["Target"];
        let saturation = bridged_saturate(&env.tin).expect("recognition core is bridge-supported");
        if std::env::var_os("KM_SAT_DEBUG").is_some() {
            let mut names: Vec<_> = env.con_id.iter().collect();
            names.sort_unstable_by_key(|(_, index)| **index);
            eprintln!(
                "MINI7914-SAT x={} target={} verdict={:?} known={:?} certain={:?} names={:?}",
                x,
                target,
                saturation.sat_verdict[x],
                saturation.known_subsumers[x],
                saturation.certain_subsumers[x],
                names
            );
        }
        assert_eq!(saturation.sat_verdict[x], Some(false));
        assert!(
            saturation.known_subsumers[x].contains(&target),
            "signed inverse-super links must carry AQ recognition back to X"
        );
        assert!(
            saturation.certain_subsumers[x]
                .as_ref()
                .is_some_and(|subsumers| subsumers.contains(&target)),
            "Konclude's extractor trusts the completed, sufficient automata label"
        );
    }

    #[test]
    fn production_read_off_populates_persistent_kpset_messages() {
        let ofn = format!(
            "{PREFIX}\\
             Declaration(Class(:A)) Declaration(Class(:B))\n\\
             SubClassOf(:A :B)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        configure_production_search(&mut algo);
        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let n = bridged.named.len();
        let mut state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &vec![None; n],
            &vec![None; n],
            &vec![Vec::new(); n],
            &(0..n).collect::<Vec<_>>(),
            ctx.ontology_arenas().concepts(),
        );
        let a = env.con_id["A"];
        let b = env.con_id["B"];
        let mut next_id = 1_000;
        let (_, _, root) =
            bridged_classify_subject_with_root(&mut algo, &mut ctx, &bridged, &mut next_id, a, n)
                .expect("deterministic A read-off");
        analyse_kpset_completion_model(&mut classifier, &mut state, a, root, &mut ctx);

        let a_item = &state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[a].index()];
        assert!(a_item.has_subsumer_concept_item(state.item_ids[b]));
        assert!(a_item.is_class_pseudo_model_initalized());
    }

    #[test]
    fn production_read_off_keeps_open_or_disjuncts_nondeterministic() {
        let ofn = format!(
            "{PREFIX}\\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\\
             SubClassOf(:A ObjectUnionOf(:B :C))\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        configure_production_search(&mut algo);
        assert!(algo.conf_build_dependencies);
        assert!(
            !algo.conf_dependency_backjumping,
            "the production classifier builds dependencies independently of DDB"
        );
        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let n = bridged.named.len();
        let mut state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &vec![None; n],
            &vec![None; n],
            &vec![Vec::new(); n],
            &(0..n).collect::<Vec<_>>(),
            ctx.ontology_arenas().concepts(),
        );
        let (a, b, c) = (env.con_id["A"], env.con_id["B"], env.con_id["C"]);
        let mut next_id = 1_000;
        let (_, authoritative, root) =
            bridged_classify_subject_with_root(&mut algo, &mut ctx, &bridged, &mut next_id, a, n)
                .expect("A has an open disjunctive model");
        assert!(
            !authoritative,
            "an opened OR branch is not a canonical model"
        );
        analyse_kpset_completion_model(&mut classifier, &mut state, a, root, &mut ctx);

        let a_item = &state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[a].index()];
        assert!(
            !a_item.has_subsumer_concept_item(state.item_ids[b])
                && !a_item.has_subsumer_concept_item(state.item_ids[c]),
            "a selected OR alternative must not be reported as a deterministic subsumer"
        );
        for candidate in [b, c] {
            assert!(
                !state
                    .candidate_state(a, candidate)
                    .is_some_and(|(confirmed, _)| confirmed),
                "an untested OR alternative must remain unconfirmed"
            );
        }
    }

    #[test]
    fn production_read_off_populates_other_node_possible_subsumptions() {
        let ofn = format!(
            "{PREFIX}\\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\\
             Declaration(ObjectProperty(:R))\n\\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        configure_production_search(&mut algo);
        let mut classifier = OptimizedKPSetClassSubsumptionClassifierThread::new();
        let n = bridged.named.len();
        let mut state = classifier.initialize_synchronous_kpset_from_saturation_data(
            &bridged.named,
            &vec![None; n],
            &vec![None; n],
            &vec![Vec::new(); n],
            &(0..n).collect::<Vec<_>>(),
            ctx.ontology_arenas().concepts(),
        );
        let a = env.con_id["A"];
        let b = env.con_id["B"];
        let c = env.con_id["C"];
        let mut next_id = 1_000;
        let (_, _, root) =
            bridged_classify_subject_with_root(&mut algo, &mut ctx, &bridged, &mut next_id, a, n)
                .expect("deterministic A read-off");
        analyse_kpset_completion_model(&mut classifier, &mut state, a, root, &mut ctx);

        let b_item = &state
            .ontology_item
            .get_concept_satisfiable_test_item_container()[state.item_ids[b].index()];
        let possible = b_item
            .get_possible_subsumption_map_ref()
            .expect("the live other-node analyser initializes B's possible map");
        assert!(possible.contains(bridged.named[c]));
    }

    /// KM_HT_UNSATCACHE integration: the learned-nogood store survives
    /// `reset_probe_env` and never flips a verdict. Drives the SAME env
    /// lifecycle as `bridged_classify` (fresh env → probe → reset → probe)
    /// with the handler installed and the DDB+unsat-cache flags set
    /// programmatically (env-var-independent, so the test is meaningful in
    /// every suite mode). Asserts: (1) an UNSAT probe stays UNSAT when
    /// re-probed against the warm cache; (2) a SAT probe on overlapping
    /// vocabulary is NOT corrupted by cache entries learned from the UNSAT
    /// one (the critical soundness control — a nogood must only fire on a
    /// label that genuinely contains it).
    #[test]
    fn unsat_cache_warm_probes_keep_verdicts() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(Class(:A1)) Declaration(Class(:A2))\n\
             Declaration(Class(:Z))\n\
             SubClassOf(:X ObjectUnionOf(:A1 :A2))\n\
             SubClassOf(:A1 :Y)\n\
             SubClassOf(:A2 :Y)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert_eq!(bridged.unsupported, 0, "fully bridged");
        install_bridge_unsat_cache(&mut ctx);
        let set_flags = |algo: &mut CompletionTaskHandleAlgorithm| {
            algo.conf_build_dependencies = true;
            algo.conf_dependency_backjumping = true;
            algo.conf_atomic_semantic_branching = true;
            algo.conf_write_unsat_caching = true;
            algo.conf_test_occur_unsat_cached = true;
        };
        set_flags(&mut algo);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        let (x, y, z) = (
            bridged.named[idx("X")],
            bridged.named[idx("Y")],
            bridged.named[idx("Z")],
        );
        let mut id = 0i64;
        // Probe 1: X ⊓ ¬Y — UNSAT (X ⊑ Y through both disjuncts); the DDB
        // analysis may write nogoods into the shared cache here.
        let cold = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(x, false), (y, true)],
        );
        assert_eq!(cold, Some(true), "X ⊑ Y must hold (cold cache)");
        // Probe 2 (warm): the same seed re-probed after the classify-style
        // reset — the carried cache must reproduce the verdict.
        reset_probe_env(&mut algo, &mut ctx, &bridged, false);
        set_flags(&mut algo);
        let warm = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(x, false), (y, true)],
        );
        assert_eq!(warm, Some(true), "X ⊑ Y must hold (warm cache)");
        // Probe 3 (warm, SAT control): X ⊓ ¬Z is satisfiable — a nogood
        // learned from the ¬Y run must not fire on this overlapping label.
        reset_probe_env(&mut algo, &mut ctx, &bridged, false);
        set_flags(&mut algo);
        let sat = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(x, false), (z, true)],
        );
        assert_eq!(sat, Some(false), "X ⊑ Z must NOT hold (warm cache)");
        // The handler must still be installed after the resets (the carry).
        assert!(
            ctx.base.take_used_unsatisfiable_cache_handler().is_some(),
            "unsat-cache handler must survive reset_probe_env"
        );
    }

    /// Miniature of the ore_ont_12653 wrong-root-cancel (memory
    /// project_km_bridge_disjunction_probe cont-11): a TOP covering
    /// `⊤ ⊑ A ⊔ B` with A,B disjoint; `A ⊑ ≤2 r.E` kills the A-branch on X
    /// (X has three pairwise-disjoint E-successors); the B-branch adds three
    /// FRESH pairwise-disjoint E-successors, and X's `≤3 r.E` then forces a
    /// 6→3 CROSS-GROUP merge matching — which EXISTS (cross pairs are
    /// compatible), so **X is SATISFIABLE** (the B-branch model) and X ⊑ Y
    /// must NOT hold for an unrelated Y. The 12653 kernel bug: the u29
    /// all-siblings-refuted propagation reads the pairing deaths' remainders
    /// as deterministic-only and wrongly ROOT-CANCELS, declaring X unsat
    /// (⇒ X ⊑ everything). Run plain AND with
    /// `KM_HT_COW=1 KM_HT_DDB=1 KM_HT_DDB_REFUTED_DISCARD=1` (the fast
    /// path that reaches the propagation); both must pass once u29's
    /// before-proc-tag remainder is fixed. `#[ignore]` while env-driven.
    #[test]
    #[ignore]
    fn covering_atmost_cross_merge_sat() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:E))\n\
             Declaration(Class(:D1)) Declaration(Class(:D2)) Declaration(Class(:D3))\n\
             Declaration(Class(:E1)) Declaration(Class(:E2)) Declaration(Class(:E3))\n\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(owl:Thing ObjectUnionOf(:A :B))\n\
             DisjointClasses(:A :B)\n\
             SubClassOf(:A ObjectMaxCardinality(2 :r :E))\n\
             SubClassOf(:B ObjectIntersectionOf(ObjectSomeValuesFrom(:r :D1) \
             ObjectSomeValuesFrom(:r :D2) ObjectSomeValuesFrom(:r :D3)))\n\
             DisjointClasses(:D1 :D2 :D3)\n\
             SubClassOf(:D1 :E) SubClassOf(:D2 :E) SubClassOf(:D3 :E)\n\
             SubClassOf(:X ObjectIntersectionOf(ObjectSomeValuesFrom(:r :E1) \
             ObjectSomeValuesFrom(:r :E2) ObjectSomeValuesFrom(:r :E3) \
             ObjectMaxCardinality(3 :r :E)))\n\
             DisjointClasses(:E1 :E2 :E3)\n\
             SubClassOf(:E1 :E) SubClassOf(:E2 :E) SubClassOf(:E3 :E)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            !env.subsumes("X", "Y"),
            "X must be satisfiable (B-branch cross-merge model) — a spurious \
             X ⊑ Y means the search wrongly refuted every covering branch \
             (the u29 wrong-root-cancel in miniature)"
        );
    }

    /// ddmin-minimal ore_ont_12653 wrong-root-cancel oracle (the leftover
    /// poisoning defect): under an Or on a successor node, alternative 1
    /// fires the node's own ≥2-expansion (creates successor nodes), so the
    /// advance cannot restore the single-node label snapshot — alt-1's
    /// disjunct SURVIVES into alternative 2's world. Alt-2's ⊥-derivation
    /// then carries connection dependencies to BOTH alternatives' track
    /// points, the u29 all-siblings-refuted propagation reads the decision
    /// as fully refuted with root-level externals only, and ROOT-CANCELS ⇒
    /// spurious AlternativePath ⊑ PathOfLength2 (a Path with three elements
    /// is a countermodel). Fixed by gating the u29 analysis — not just the
    /// DDB stack walk — on `unrestored_advance_count == 0` (u02). Passes in
    /// plain mode by construction; the KM_HT_DDB=1 matrix leg is the
    /// regression proof.
    #[test]
    fn unrestored_advance_leftover_no_root_cancel() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:AlternativePath)) Declaration(Class(:Path))\n\
             Declaration(Class(:MainPath)) Declaration(Class(:PathElement))\n\
             Declaration(Class(:PathOfLength2))\n\
             Declaration(ObjectProperty(:hasPathElement))\n\
             SubClassOf(:AlternativePath :Path)\n\
             EquivalentClasses(:MainPath ObjectIntersectionOf(\
             ObjectComplementOf(:AlternativePath) :Path))\n\
             SubClassOf(:Path ObjectMinCardinality(2 :hasPathElement :PathElement))\n\
             DisjointClasses(:Path :PathElement)\n\
             EquivalentClasses(:PathOfLength2 ObjectExactCardinality(2 :hasPathElement :PathElement))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // Under the plain-mode multi-node completeness gate this probe's SAT
        // verdict becomes a DEFER (None) — acceptable. The regression this
        // test guards is the WRONG UNSAT (Some(true)) from the poisoned u29
        // analysis.
        assert_ne!(
            env.try_subsumes("AlternativePath", "PathOfLength2"),
            Some(true),
            "AlternativePath ⊑ PathOfLength2 must NOT hold (3-element Path \
             countermodel) — a spurious UNSAT here means the u29 analysis ran \
             on leftover-poisoned state after an unrestored advance"
        );
    }

    #[test]
    fn bridge_disjunction_by_cases() {
        // A ⊑ B ⊔ C, B ⊑ D, C ⊑ D ⇒ A ⊑ D — exercises the OR rule + the
        // sound same-node backtrack through the BRIDGED encoding.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             SubClassOf(:A ObjectUnionOf(:B :C))\n\
             SubClassOf(:B :D)\n\
             SubClassOf(:C :D)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(env.subsumes("A", "D"), "A ⊑ D by reasoning by cases");
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
    }

    #[test]
    fn bridge_disjunction_open_branch() {
        // Drop C ⊑ D: the C branch stays open ⇒ A ⊑ D must NOT hold (the
        // negative control that pinned the chronological-backtrack bug).
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             SubClassOf(:A ObjectUnionOf(:B :C))\n\
             SubClassOf(:B :D)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            !env.subsumes("A", "D"),
            "A ⊑ D must NOT hold (C branch open)"
        );
    }

    /// Dump every node's label tags (diagnostic, used on failure only).
    fn dump_nodes(env: &mut BridgeEnv, label: &str) {
        let ctx = env.ctx.as_mut().expect("a probe ran");
        let n = ctx.process_context().node_count();
        eprintln!("DBG {label}: {n} nodes");
        for i in 0..n {
            let node = super::super::process::NodeId::new(i as Cint64);
            let ls = ctx
                .process_context_mut()
                .node_reapply_concept_label_set(node);
            let mut tags: Vec<_> = ctx
                .process_context()
                .label_set(ls)
                .concept_des_dep_map
                .keys()
                .copied()
                .collect();
            tags.sort_unstable();
            eprintln!("DBG   node {i}: tags {tags:?}");
        }
    }

    #[test]
    fn bridge_exists_forall_clash() {
        // A ⊑ ∃R.B, A ⊑ ∀R.C, B ⊓ C ⊑ ⊥(via D/¬D)  ⇒ A unsatisfiable ⇒ A ⊑ E
        // for the probe; simpler direct check: A ⊑ ∃R.B and ∀R.¬B ⇒ A ⊓ that
        // ∀ is unsat. Encode as: A ⊑ ∃R.B, F ⊑ ∀R.C with B ⊓ C contradictory.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:R))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\
             SubClassOf(:A ObjectAllValuesFrom(:R :C))\n\
             SubClassOf(:B ObjectComplementOf(:C))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // A forces an R-successor with B (∃), propagates C (∀), and B ⊑ ¬C
        // clashes on the successor ⇒ A is unsatisfiable ⇒ A ⊑ B holds
        // vacuously (any subsumption from an unsat concept).
        let holds = env.subsumes("A", "B");
        if !holds {
            dump_nodes(&mut env, "after A⊑B probe");
        }
        assert!(holds, "A unsat ⇒ A ⊑ B vacuously");
        let bc = env.subsumes("B", "C");
        if bc {
            // XXX-DBG: spurious unsat — show the TInput + the final graph
            for (i, n) in env.tin.concepts.iter().enumerate() {
                eprintln!("DBG concept {i} = {n}");
            }
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}C{c}({t})", if *neg { "¬" } else { "" })
                    }
                }
            };
            for (i, cl) in env.tin.clauses.iter().enumerate() {
                let b: Vec<String> = cl.body.iter().map(show).collect();
                let h: Vec<String> = cl.head.iter().map(show).collect();
                eprintln!("DBG clause {i}: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            }
            dump_nodes(&mut env, "after B⊑C probe");
        }
        assert!(!bc, "B ⊑ C must NOT hold");
    }

    #[test]
    fn bridge_role_hierarchy_forall() {
        // R ⊑ S: A ⊑ ∃R.D, A ⊑ ∀S.C, D ⊑ ¬C — the ∀S restriction must reach
        // the R-successor via the hierarchy ⇒ A unsatisfiable. The bridged
        // counterpart of the `role_hierarchy_forall` selftest, driven from
        // real OWL through the indirect-super-role linkers pass.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:R)) Declaration(ObjectProperty(:S))\n\
             SubObjectPropertyOf(:R :S)\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :D))\n\
             SubClassOf(:A ObjectAllValuesFrom(:S :C))\n\
             SubClassOf(:D ObjectComplementOf(:C))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        let holds = env.subsumes("A", "D");
        if !holds {
            dump_nodes(&mut env, "after A⊑D probe (hierarchy)");
        }
        assert!(holds, "A unsat via R⊑S hierarchy ⇒ A ⊑ D vacuously");
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
    }

    /// Role DOMAIN through a forced successor (the ore_ont_9635 gap):
    /// `Domain(r, D)` + `A ⊑ ∃r.⊤` entails `A ⊑ D` DETERMINISTICALLY —
    /// the successor's existence fires the domain clause on the edge.
    /// The 9635 shape adds exact cardinality; test both.
    #[test]
    fn bridge_domain_via_forced_successor() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D)) Declaration(Class(:T))\n\
             Declaration(ObjectProperty(:r))\n\
             ObjectPropertyDomain(:r :D)\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :T))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        assert!(
            env.subsumes("A", "D"),
            "A ⊑ D via domain(r)=D and A's forced r-successor"
        );
        assert!(!env.subsumes("D", "A"), "D ⊑ A must NOT hold");
        // the 9635 shape: exact cardinality forces the successor
        let ofn2 = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             ObjectPropertyDomain(:r :D)\n\
             SubClassOf(:A ObjectExactCardinality(1 :r))\n)"
        );
        let mut env2 = bridge_ofn(&ofn2);
        assert!(
            env2.subsumes("A", "D"),
            "A ⊑ D via domain(r)=D and A's =1 r-successor"
        );
    }

    /// The ore_ont_9635 completeness gap (ddmin, 294 → 2+2 axioms): the
    /// domain entailment `A ⊑ =1 r` + `Domain(r, D)` ⇒ `A ⊑ D` (covered
    /// bare by `bridge_domain_via_forced_successor`) MUST survive the
    /// presence of unrelated DataHasValue axioms — their value-identity
    /// clausification introduces singleton concepts, and the singleton
    /// path broke the pairwise probe (`unsat(A ⊓ ¬D)` found a spurious
    /// model: pairwise=false while readoff_has=true).
    #[test]
    fn bridge_domain_survives_datatype_singletons() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:D)) Declaration(Class(:I))\n\
             Declaration(Class(:P)) Declaration(Class(:L)) Declaration(Class(:RL))\n\
             Declaration(ObjectProperty(:r)) Declaration(ObjectProperty(:h))\n\
             Declaration(DataProperty(:v))\n\
             SubClassOf(:A ObjectExactCardinality(1 :r))\n\
             ObjectPropertyDomain(:r :D)\n\
             EquivalentClasses(:P ObjectIntersectionOf(\
             DataHasValue(:v \"true\"^^xsd:boolean) :I))\n\
             EquivalentClasses(:L ObjectIntersectionOf(\
             ObjectAllValuesFrom(:h :P) :RL))\n)"
        );
        let mut env = bridge_ofn(&ofn);
        // The cross-branch wipe DETECTOR turns the previously-WRONG SAT
        // verdict into a DEFER (None) — acceptable: the production driver
        // then defers the subject and the caller falls back to a complete
        // arm. `Some(false)` (the wrong verdict) is the regression.
        let verdict = env.try_subsumes("A", "D");
        let holds = verdict == Some(true);
        if verdict == Some(false) {
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => format!(
                        "{}{}({t})",
                        if *neg { "¬" } else { "" },
                        env.tin.concepts.get(*c).map(String::as_str).unwrap_or("?")
                    ),
                    HAtom::Role { r, s, t } => {
                        format!(
                            "{}({s},{t})",
                            env.tin.roles.get(*r).map(String::as_str).unwrap_or("?")
                        )
                    }
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => format!(
                        "∃{}.{}{}({t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"),
                        if *neg { "¬" } else { "" },
                        env.tin.concepts.get(*c).map(String::as_str).unwrap_or("?")
                    ),
                }
            };
            for (i, cl) in env.tin.clauses.iter().enumerate() {
                let b: Vec<String> = cl.body.iter().map(show).collect();
                let h: Vec<String> = cl.head.iter().map(show).collect();
                eprintln!("DBG clause {i}: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
            }
            for (i, n) in env.tin.concepts.iter().enumerate() {
                eprintln!("DBG concept idx {i} = tag {} = {n}", 10 + i);
            }
            for (i, n) in env.tin.roles.iter().enumerate() {
                eprintln!("DBG role idx {i} = arena-tag {} = {n}", 100 + i);
            }
            dump_nodes(&mut env, "after A⊑D probe (datatype singleton)");
        }
        assert_ne!(
            verdict,
            Some(false),
            "A ⊑ D holds (domain via forced successor): answering NOT-subsumed is unsound; \
             DEFER (None) is the acceptable degradation, deriving it the aspirational fix"
        );
        let _ = holds;
        assert_ne!(
            env.try_subsumes("D", "A"),
            Some(true),
            "D ⊑ A must NOT hold"
        );
    }

    #[test]
    fn bridge_exists_recognition_inverse() {
        // ∃R.B ⊑ Q (the definer-recognition / absorption shape, frontend-
        // clausified to `B(y) ∧ R(x,y) → Q(x)`, bridged as `B ⊑ ∀R⁻.Q`):
        // A ⊑ ∃R.B and Q ⊑ E ⊢ A ⊑ E — the Q lands on A through the
        // inverse-edge propagation, not through any forward unfold.
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:Q)) Declaration(Class(:E))\n\
             Declaration(ObjectProperty(:R))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:R :B))\n\
             SubClassOf(ObjectSomeValuesFrom(:R :B) :Q)\n\
             SubClassOf(:Q :E)\n)"
        );
        let mut env = bridge_ofn(&ofn);
        let holds = env.subsumes("A", "E");
        if !holds {
            dump_nodes(&mut env, "after A⊑E probe (recognition)");
        }
        assert!(
            holds,
            "A ⊑ E via ∃R.B ⊑ Q recognition over the inverse edge"
        );
        assert!(!env.subsumes("E", "A"), "E ⊑ A must NOT hold");
    }

    /// Scale smoke-test on a REAL ontology: bridge `KM_BRIDGE_ONT` and run
    /// satisfiability probes for the first `KM_BRIDGE_PROBES` (default 3)
    /// named non-internal concepts, timing each. Measures whether the ported
    /// engine + re-drive harness converge at real-TBox scale and what a probe
    /// costs — the data for the classify-driver design (per-task databox vs
    /// per-probe rebuild, reapply-queue priority). Diagnostic only.
    #[test]
    #[ignore]
    fn bridge_scale_probe() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let n_probes: usize = std::env::var("KM_BRIDGE_PROBES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named_set,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let subjects: Vec<usize> = tin
            .concepts
            .iter()
            .enumerate()
            .filter(|(_, n)| named_set.contains(*n))
            .map(|(i, _)| i)
            .take(n_probes)
            .collect();
        for &s in &subjects {
            let t0 = std::time::Instant::now();
            let mut algo = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo);
            let mut ctx = CalculationAlgorithmContextBase::new();
            ctx.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx.ontology_arenas_mut().alloc_concept(c)
            };
            ctx.processing_data_box_mut().ontology_top_concept = top;
            let bridged = bridge_tinput(&mut ctx, &tin);
            let t_bridge = t0.elapsed();
            let t1 = std::time::Instant::now();
            let mut next = 0i64;
            let verdict = bridged_unsat(
                &mut algo,
                &mut ctx,
                &bridged,
                &mut next,
                &[(bridged.named[s], false)],
            );
            eprintln!(
                "BRIDGE-PROBE {}: verdict={:?} bridge={:.0}ms probe={:.0}ms nodes={} backtracks={} absorbed={} top={}",
                tin.concepts[s],
                verdict,
                t_bridge.as_secs_f64() * 1e3,
                t1.elapsed().as_secs_f64() * 1e3,
                ctx.process_context().node_count(),
                algo.or_backtrack_count,
                bridged.absorbed,
                bridged.top_attached,
            );
        }
    }

    /// Verdict CORRECTNESS on a REAL ontology vs a gold classification.
    /// `KM_BRIDGE_ONT` = the .owl; `KM_BRIDGE_GOLD` = the `km classify` JSON
    /// output (`{"consistent":..,"subsumptions":[[sub_iri,sup_iri],..]}`,
    /// the validated production path). Samples the first `KM_BRIDGE_PROBES`
    /// (default 20) named subjects; for each, checks EVERY gold super
    /// (bridge must report subsumption) and an equal number of gold
    /// NON-supers (bridge must NOT). Reports missing (incomplete) / spurious
    /// (unsound) counts. Diagnostic; asserts only that unsound==0 when the
    /// bridge is fully covered (`unsupported==0`), since a clash verdict is
    /// sound even under-approximated.
    #[test]
    #[ignore]
    fn bridge_correctness_sample() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let n_probes: usize = std::env::var("KM_BRIDGE_PROBES")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(20);
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        // local name after '#' or last '/'.
        let local =
            |iri: &str| -> String { iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string() };
        // gold super-map: sub_local → set(sup_local); `gold_universe` = every
        // concept gold tracks (as sub or sup). Negatives are drawn ONLY from
        // this universe: cb_to_ht mints internal DEFINER concepts (Q_NNNN) that
        // are NOT named classes, so gold never lists them as supers — a subject
        // legitimately subsumed by an internal definer is correct, not unsound,
        // and must not be sampled as a negative.
        let mut supers: std::collections::HashMap<String, std::collections::HashSet<String>> =
            std::collections::HashMap::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            supers.entry(sub).or_default().insert(sup);
        }

        let mut env = bridge_ofn_path(&path);
        // owned snapshot of the TInput concept names (avoids holding an
        // immutable borrow of env across the &mut env.subsumes() calls).
        let present: std::collections::HashSet<String> = env.con_id.keys().cloned().collect();
        // subjects: gold subjects that ARE present in the TInput (in-fragment).
        let mut subjects: Vec<String> = supers
            .keys()
            .filter(|s| present.contains(*s))
            .cloned()
            .collect();
        subjects.sort();
        subjects.truncate(n_probes);

        // deterministic "random" negatives: stride through the gold-known,
        // in-fragment concepts (excludes cb_to_ht internal definers).
        let mut all_concepts: Vec<String> = present
            .iter()
            .filter(|c| gold_universe.contains(*c))
            .cloned()
            .collect();
        all_concepts.sort();

        let mut missing = 0usize; // gold super the bridge did NOT derive (incomplete)
        let mut spurious = 0usize; // non-super the bridge DID derive (unsound)
        let mut checked_pos = 0usize;
        let mut checked_neg = 0usize;
        for sub in &subjects {
            let gold_sups = &supers[sub];
            for sup in gold_sups {
                if !present.contains(sup) || sup == sub {
                    continue;
                }
                checked_pos += 1;
                if !env.subsumes(sub, sup) {
                    missing += 1;
                    if missing <= 20 {
                        eprintln!("MISSING (incomplete): {sub} ⊑ {sup}");
                    }
                }
            }
            // negatives: same count of concepts NOT in the gold super-set.
            let want_neg = gold_sups.len().max(1);
            let mut got = 0usize;
            let step = (all_concepts.len() / want_neg.max(1)).max(1);
            let mut i = 0usize;
            while got < want_neg && i < all_concepts.len() {
                let cand = &all_concepts[i];
                i += step;
                if cand == sub || gold_sups.contains(cand) {
                    continue;
                }
                checked_neg += 1;
                got += 1;
                if env.subsumes(sub, cand) {
                    spurious += 1;
                    if spurious <= 20 {
                        eprintln!("SPURIOUS (unsound): {sub} ⊑ {cand}");
                    }
                }
            }
        }
        eprintln!(
            "BRIDGE-CORRECTNESS {path}: subjects={} pos_checked={} missing={} \
             neg_checked={} spurious={} unsupported={}",
            subjects.len(),
            checked_pos,
            missing,
            checked_neg,
            spurious,
            env.unsupported,
        );
        if env.unsupported == 0 {
            assert_eq!(spurious, 0, "clash verdicts must be sound");
        }
    }

    /// Compare the two subsumption oracles on ONE pair (`KM_BRIDGE_PAIR=
    /// "SubLocal,SupLocal"`): the pairwise probe (`subsumes`, seed A+¬B,
    /// re-drive with backtrack) vs the model read-off (`bridged_classify_
    /// subject`, saturate {A} and read the root label). Tells whether a
    /// read-off MISS is a read-off limitation (pairwise=true) or a real
    /// completion-incompleteness (both false). Diagnostic.
    #[test]
    #[ignore]
    fn bridge_probe_pair() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let pair = std::env::var("KM_BRIDGE_PAIR").expect("set KM_BRIDGE_PAIR=Sub,Sup");
        let (sub, sup) = pair.split_once(',').expect("Sub,Sup");
        let mut env = bridge_ofn_path(&path);
        // KM_BRIDGE_DUMP_NAMES: print the concept TAG of each listed name so a
        // numeric KM_BRIDGE_FIND_TAG follow-up can watch the chain.
        // KM_BRIDGE_DUMP_ROLE_SUPERS=<role-name>: print the bridged indirect
        // super-role list (as role TAGS: 100+i forward, 100+n_roles+i inverse)
        // for the named role — verifies the pass-1 hierarchy closure.
        if let Ok(rn) = std::env::var("KM_BRIDGE_DUMP_ROLE_SUPERS") {
            for (i, name) in env.tin.roles.iter().enumerate() {
                if name == &rn {
                    // rebuild a bridged env to inspect the arena role objects
                    let mut ctxr = CalculationAlgorithmContextBase::new();
                    let topr = {
                        let mut c = Concept::new();
                        c.set_concept_tag(1);
                        c.set_operator_code(op::CCTOP);
                        ctxr.ontology_arenas_mut().alloc_concept(c)
                    };
                    ctxr.processing_data_box_mut().ontology_top_concept = topr;
                    let br = bridge_tinput(&mut ctxr, &env.tin);
                    let robj = br.roles[i];
                    let sup_tags: Vec<Cint64> = ctxr
                        .ontology_arenas()
                        .role(robj)
                        .indirect_super_roles
                        .iter()
                        .map(|l| ctxr.ontology_arenas().role(l.target).get_role_tag())
                        .collect();
                    let n = env.tin.roles.len() as Cint64;
                    let named_sups: Vec<String> = sup_tags
                        .iter()
                        .map(|&t| {
                            let fwd = t - 100;
                            if fwd < n {
                                env.tin.roles[fwd as usize].clone()
                            } else {
                                format!("INV({})", env.tin.roles[(fwd - n) as usize])
                            }
                        })
                        .collect();
                    let complex: Vec<(Cint64, bool)> = std::iter::once(robj)
                        .chain(
                            ctxr.ontology_arenas()
                                .role(robj)
                                .indirect_super_roles
                                .iter()
                                .map(|link| link.target),
                        )
                        .map(|role| {
                            let r = ctxr.ontology_arenas().role(role);
                            (r.get_role_tag(), r.is_complex_role())
                        })
                        .collect();
                    eprintln!(
                        "ROLE-SUPERS {rn} (tag {}): {:?} complex={complex:?}",
                        100 + i,
                        named_sups
                    );
                }
            }
        }
        // KM_BRIDGE_TAG_NAMES=<tag>[,<tag>...]: reverse map concept TAGs to
        // TInput names (tag = TAG_BASE + index).
        if let Ok(tags) = std::env::var("KM_BRIDGE_TAG_NAMES") {
            for t in tags.split(',') {
                if let Ok(tag) = t.trim().parse::<i64>() {
                    let i = (tag - TAG_BASE) as usize;
                    if i < env.tin.concepts.len() {
                        eprintln!("TAG-NAME {}={}", tag, env.tin.concepts[i]);
                    }
                }
            }
        }
        // KM_BRIDGE_GREP_CLAUSES=<c:IDX|r:IDX>[,...]: print every TInput
        // clause mentioning any listed concept (c:) or role (r:) index,
        // with concept names resolved — the clause-level entailment-check
        // input (the UNSUP-dumper format).
        if let Ok(spec) = std::env::var("KM_BRIDGE_GREP_CLAUSES") {
            let mut cons: Vec<usize> = Vec::new();
            let mut rols: Vec<usize> = Vec::new();
            for part in spec.split(',') {
                let part = part.trim();
                if let Some(i) = part.strip_prefix("c:").and_then(|s| s.parse().ok()) {
                    cons.push(i);
                } else if let Some(i) = part.strip_prefix("r:").and_then(|s| s.parse().ok()) {
                    rols.push(i);
                }
            }
            let name =
                |c: usize| -> &str { env.tin.concepts.get(c).map(String::as_str).unwrap_or("?") };
            let show = |a: &crate::orchestrate::cb_to_ht::HAtom| -> String {
                use crate::orchestrate::cb_to_ht::HAtom;
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                    HAtom::Role { r, s, t } => format!(
                        "{}({s},{t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?")
                    ),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => format!(
                        "∃{}.{}{}({t})",
                        env.tin.roles.get(*r).map(String::as_str).unwrap_or("?"),
                        if *neg { "¬" } else { "" },
                        name(*c)
                    ),
                }
            };
            for cl in &env.tin.clauses {
                use crate::orchestrate::cb_to_ht::HAtom;
                let hit = cl.body.iter().chain(cl.head.iter()).any(|a| match a {
                    HAtom::Concept { c, .. } | HAtom::Exist { c, .. } => cons.contains(c),
                    HAtom::Role { r, .. } => rols.contains(r),
                    HAtom::Eq { .. } => false,
                }) || cl.body.iter().chain(cl.head.iter()).any(|a| match a {
                    HAtom::Exist { r, .. } => rols.contains(r),
                    _ => false,
                });
                if hit {
                    let b: Vec<String> = cl.body.iter().map(show).collect();
                    let h: Vec<String> = cl.head.iter().map(show).collect();
                    eprintln!("CLAUSE: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
                }
            }
        }
        // KM_BRIDGE_ROLE_NAMES=<idx>[,<idx>...]: print TInput role names.
        if let Ok(idxs) = std::env::var("KM_BRIDGE_ROLE_NAMES") {
            for i in idxs.split(',') {
                if let Ok(i) = i.trim().parse::<usize>() {
                    if i < env.tin.roles.len() {
                        eprintln!("ROLE-NAME {}={}", i, env.tin.roles[i]);
                    }
                }
            }
        }
        if let Ok(names) = std::env::var("KM_BRIDGE_DUMP_NAMES") {
            for n in names.split(',') {
                if let Some(&idx) = env.con_id.get(n.trim()) {
                    eprintln!("NAME-TAG {}={}", n.trim(), TAG_BASE + idx as Cint64);
                }
            }
        }
        let pairwise = env.subsumes(sub, sup);

        // read-off on the same subject
        let n_named = env.tin.concepts.len();
        let s_idx = *env.con_id.get(sub).expect("sub in TInput");
        let sup_idx = *env.con_id.get(sup).expect("sup in TInput");
        let mut algo = CompletionTaskHandleAlgorithm::new();
        configure_default_blocking(&mut algo);
        if std::env::var_os("KM_HT_BUILD_DEPENDENCIES").is_some() {
            algo.conf_build_dependencies = true;
        }
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let top = {
            let mut c = Concept::new();
            c.set_concept_tag(1);
            c.set_operator_code(op::CCTOP);
            ctx.ontology_arenas_mut().alloc_concept(c)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &env.tin);
        if let Ok(spec) = std::env::var("KM_BRIDGE_DUMP_CONCEPT_TAGS") {
            let wanted: BTreeSet<Cint64> = spec
                .split(',')
                .filter_map(|s| s.trim().parse().ok())
                .collect();
            for i in 0..ctx.ontology_arenas().concept_count() {
                let concept = ConceptId::new(i);
                let c = ctx.ontology_arenas().concept(concept);
                let tag = c.get_concept_tag();
                if !wanted.contains(&tag) {
                    continue;
                }
                let role = c.get_role();
                let role_tag = role
                    .is_some()
                    .then(|| ctx.ontology_arenas().role(role).get_role_tag());
                let operands: Vec<String> = c
                    .get_operand_list()
                    .iter()
                    .map(|link| {
                        format!(
                            "{}{}",
                            if link.negated { "not " } else { "" },
                            ctx.ontology_arenas().concept(link.target).get_concept_tag()
                        )
                    })
                    .collect();
                eprintln!(
                    "CONCEPT-TAG tag={tag} op={} role={role_tag:?} operands=[{}]",
                    c.get_operator_code(),
                    operands.join(" ")
                );
            }
        }
        let mut next = 0i64;
        let readoff =
            bridged_classify_subject(&mut algo, &mut ctx, &bridged, &mut next, s_idx, n_named);
        let readoff_has = readoff
            .as_ref()
            .map(|(subs, _)| subs.contains(&sup_idx))
            .unwrap_or(false);
        eprintln!(
            "BRIDGE-PAIR {sub} ⊑ {sup}: pairwise={pairwise} readoff_has={readoff_has} \
             readoff_nondet={}",
            !readoff.as_ref().map(|(_, auth)| *auth).unwrap_or(false),
        );
        if std::env::var_os("KM_BRIDGE_PROD_PAIR").is_some() {
            let production = bridged_classify(&env.tin).expect("production classification");
            let production_has = production.subsumptions.contains(&(s_idx, sup_idx));
            eprintln!("BRIDGE-PRODUCTION-PAIR {sub} ⊑ {sup}: production_has={production_has}");
            assert!(
                production_has,
                "Konclude's post-satisfiability possible-subsumption map must be tested"
            );
        }
        // dump every clause referencing sub or sup (to scope the propagation
        // the completion is missing).
        if std::env::var("KM_BRIDGE_DUMP_CLAUSES").is_ok() {
            let name = |i: usize| env.tin.concepts[i].as_str();
            let show = |a: &HAtom| -> String {
                match a {
                    HAtom::Concept { neg, c, t } => {
                        format!("{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                    HAtom::Role { r, s, t } => format!("R{r}({s},{t})"),
                    HAtom::Eq { s, t } => format!("eq({s},{t})"),
                    HAtom::Exist { r, neg, c, t } => {
                        format!("∃R{r}.{}{}({t})", if *neg { "¬" } else { "" }, name(*c))
                    }
                }
            };
            let mentions = |cl: &HtClause, idx: usize| -> bool {
                cl.body.iter().chain(cl.head.iter()).any(|a| {
                    matches!(a,
                    HAtom::Concept { c, .. } | HAtom::Exist { c, .. } if *c == idx)
                })
            };
            // extra names to trace (KM_BRIDGE_DUMP_NAMES="Q_708,Q_266").
            let extra_idx: Vec<usize> = std::env::var("KM_BRIDGE_DUMP_NAMES")
                .ok()
                .map(|s| {
                    s.split(',')
                        .filter_map(|n| env.con_id.get(n.trim()).copied())
                        .collect()
                })
                .unwrap_or_default();
            for cl in &env.tin.clauses {
                if mentions(cl, s_idx)
                    || mentions(cl, sup_idx)
                    || extra_idx.iter().any(|&i| mentions(cl, i))
                {
                    let b: Vec<String> = cl.body.iter().map(show).collect();
                    let h: Vec<String> = cl.head.iter().map(show).collect();
                    eprintln!("  CLAUSE: {} -> {}", b.join(" ∧ "), h.join(" ∨ "));
                }
            }
        }
    }

    /// FULL model-read-off classification vs gold: saturate every named
    /// subject ONCE (`bridged_classify_subject`) and read its subsumers off
    /// the root label — O(concepts) saturations, the feasible classification
    /// path (naive pairwise on 1016 = ~2500² probes). Compares the WHOLE
    /// derived named-subsumption relation to the `km classify` gold
    /// (`KM_BRIDGE_GOLD`), reporting missing (incomplete) / spurious
    /// (unsound) / non-deterministic-subject counts. Diagnostic.
    #[test]
    #[ignore]
    fn bridge_classify_full() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        let local =
            |iri: &str| -> String { iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string() };
        let mut gold_pairs: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        // Names appearing as a SUB in gold: only these become subjects, so a
        // gold file restricted to a subject sample stays self-consistent —
        // every admitted subject carries its COMPLETE supers set, keeping
        // `spurious` meaningful (a supers-only name would otherwise be
        // classified against an empty gold row and misread as unsound).
        let mut gold_subs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_subs.insert(sub.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named_set,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let n_named = tin.concepts.len();

        let mut algo = CompletionTaskHandleAlgorithm::new();
        configure_default_blocking(&mut algo);
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let top = {
            let mut c = Concept::new();
            c.set_concept_tag(1);
            c.set_operator_code(op::CCTOP);
            ctx.ontology_arenas_mut().alloc_concept(c)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &tin);

        // subjects = gold-classified (sub-side), in-fragment named concepts.
        let mut subjects: Vec<usize> = (0..n_named)
            .filter(|&i| gold_subs.contains(&tin.concepts[i]))
            .collect();
        // KM_BRIDGE_MAX_SUBJECTS=N: validate a bounded prefix of subjects
        // (correctness sample on deep taxonomies where full O(subjects)
        // classification without databox reuse is a separate speed lever).
        // When set, gold is restricted to these subjects so missing/spurious
        // stay meaningful on the sample.
        if let Some(cap) = std::env::var("KM_BRIDGE_MAX_SUBJECTS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
        {
            subjects.truncate(cap);
        }
        // pairwise-fallback COLUMNS: every gold-known named concept (a super
        // like `Path` need not be a classified subject itself).
        let targets: Vec<usize> = (0..n_named)
            .filter(|&i| gold_universe.contains(&tin.concepts[i]))
            .collect();

        let mut derived: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut nondet = 0usize;
        let mut next = 0i64;
        let t0 = std::time::Instant::now();
        for &s in &subjects {
            // fresh ctx per subject (per-probe isolation; the databox-COW
            // reuse is the next wave). Rebuild is O(TBox).
            let mut algo2 = CompletionTaskHandleAlgorithm::new();
            configure_default_blocking(&mut algo2);
            let mut ctx2 = CalculationAlgorithmContextBase::new();
            ctx2.base.used_concept_priority_strategy =
                Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
            let top2 = {
                let mut c = Concept::new();
                c.set_concept_tag(1);
                c.set_operator_code(op::CCTOP);
                ctx2.ontology_arenas_mut().alloc_concept(c)
            };
            ctx2.processing_data_box_mut().ontology_top_concept = top2;
            let bridged2 = bridge_tinput(&mut ctx2, &tin);
            // thread the singleton (value-identity) concepts — WITHOUT them
            // the kernel under-merges value nodes and unsat proofs that need
            // the merges cannot close (measured: PathOfLength3 ⊑ Path
            // converged in the probe harness, which threads them, but burned
            // its whole budget in this loop, which did not).
            algo2.singleton_concepts = bridged2.singleton_concepts.clone();
            let mut n2 = 0i64;
            let t_subj = std::time::Instant::now();
            let verdict =
                bridged_classify_subject(&mut algo2, &mut ctx2, &bridged2, &mut n2, s, n_named);
            eprintln!(
                "SUBJ {} {}: {} in {:.1}s (nodes={} backtracks={})",
                s,
                tin.concepts[s],
                match &verdict {
                    Some((v, true)) => format!("readoff {} supers", v.len()),
                    Some((v, false)) => format!("NONDET {} candidates", v.len()),
                    None => "STOP".into(),
                },
                t_subj.elapsed().as_secs_f64(),
                ctx2.process_context().node_count(),
                algo2.or_backtrack_count,
            );
            match verdict {
                Some((subs, true)) => {
                    for sup in subs {
                        if sup == s {
                            continue;
                        }
                        // only named-vs-named, gold-known targets
                        if gold_universe.contains(&tin.concepts[sup]) {
                            derived.insert((tin.concepts[s].clone(), tin.concepts[sup].clone()));
                        }
                    }
                }
                Some((cands, false)) => {
                    // Non-deterministic saturation: the one-model read-off is
                    // not authoritative — its positives are the CANDIDATE
                    // subsumers (Konclude's possible-subsumer extraction).
                    // Verify each with a pairwise probe: `unsat(s ⊓ ¬sup)`
                    // proves `s ⊑ sup` under ANY branch discipline. On a
                    // small gold universe, probe every target instead (the
                    // candidate label can under-approximate; the pairwise
                    // verdict itself is exact either way).
                    nondet += 1;
                    let cand_list: Vec<usize> = if targets.len() <= 64 {
                        targets.clone()
                    } else {
                        cands
                    };
                    for sup in cand_list {
                        if sup == s || !gold_universe.contains(&tin.concepts[sup]) {
                            continue;
                        }
                        let tp0 = std::time::Instant::now();
                        if std::env::var_os("KM_BRIDGE_PROGRESS").is_some() {
                            eprintln!("PAIR-START {} vs {}", tin.concepts[s], tin.concepts[sup]);
                        }
                        let mut algo3 = CompletionTaskHandleAlgorithm::new();
                        configure_default_blocking(&mut algo3);
                        let mut ctx3 = CalculationAlgorithmContextBase::new();
                        ctx3.base.used_concept_priority_strategy =
                            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
                        let top3 = {
                            let mut c = Concept::new();
                            c.set_concept_tag(1);
                            c.set_operator_code(op::CCTOP);
                            ctx3.ontology_arenas_mut().alloc_concept(c)
                        };
                        ctx3.processing_data_box_mut().ontology_top_concept = top3;
                        let bridged3 = bridge_tinput(&mut ctx3, &tin);
                        // value-identity singletons (see the subject loop).
                        algo3.singleton_concepts = bridged3.singleton_concepts.clone();
                        let mut n3 = 0i64;
                        if bridged_unsat(
                            &mut algo3,
                            &mut ctx3,
                            &bridged3,
                            &mut n3,
                            &[(bridged3.named[s], false), (bridged3.named[sup], true)],
                        ) == Some(true)
                        {
                            derived.insert((tin.concepts[s].clone(), tin.concepts[sup].clone()));
                        }
                        // Surface slow pair probes (the read-offs are ms; a
                        // probe that takes seconds is the scaling story).
                        let dt = tp0.elapsed();
                        if dt.as_millis() > 500 {
                            eprintln!(
                                "SLOW-PAIR {} vs {}: {:.1}s (backtracks={})",
                                tin.concepts[s],
                                tin.concepts[sup],
                                dt.as_secs_f64(),
                                algo3.or_backtrack_count,
                            );
                        }
                    }
                }
                None => nondet += 1, // STOP: no verdict at all
            }
        }
        let elapsed = t0.elapsed();
        let _ = (&algo, &bridged, &mut next);

        // restrict gold to the same subject/target universe we classified.
        let subj_names: std::collections::HashSet<String> =
            subjects.iter().map(|&i| tin.concepts[i].clone()).collect();
        let gold_restricted: std::collections::HashSet<(String, String)> = gold_pairs
            .iter()
            .filter(|(sub, sup)| subj_names.contains(sub) && gold_universe.contains(sup))
            .cloned()
            .collect();
        let missing: Vec<_> = gold_restricted.difference(&derived).take(20).collect();
        let spurious: Vec<_> = derived.difference(&gold_restricted).take(20).collect();
        for m in &missing {
            eprintln!("MISSING (incomplete): {} ⊑ {}", m.0, m.1);
        }
        for sp in &spurious {
            eprintln!("SPURIOUS (unsound): {} ⊑ {}", sp.0, sp.1);
        }
        eprintln!(
            "BRIDGE-CLASSIFY {path}: subjects={} nondet={} derived={} gold={} \
             missing={} spurious={} elapsed={:.1}s unsupported={}",
            subjects.len(),
            nondet,
            derived.len(),
            gold_restricted.len(),
            gold_restricted.difference(&derived).count(),
            derived.difference(&gold_restricted).count(),
            elapsed.as_secs_f64(),
            bridged.unsupported,
        );
    }

    /// PRODUCTION-PATH gold driver: run the shipped entry point
    /// `bridged_classify` (single reused env, production DDB search,
    /// per-subject defer + budget-escalating retry rounds) on
    /// `KM_BRIDGE_ONT` and diff the result against `KM_BRIDGE_GOLD` —
    /// the same gold format as `bridge_classify_full`, which by contrast
    /// drives the subject/probe layers directly with fresh envs. Restrict
    /// subjects via `queries` when `KM_BRIDGE_MAX_SUBJECTS` is set.
    #[test]
    #[ignore]
    fn bridge_classify_prod() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let gold_path = std::env::var("KM_BRIDGE_GOLD").expect("set KM_BRIDGE_GOLD=<json>");
        let gold_text = std::fs::read_to_string(&gold_path).expect("readable gold");
        let gold: serde_json::Value = serde_json::from_str(&gold_text).expect("gold json");
        let local =
            |iri: &str| -> String { iri.rsplit(['#', '/']).next().unwrap_or(iri).to_string() };
        let mut gold_pairs: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        let mut gold_universe: std::collections::HashSet<String> = std::collections::HashSet::new();
        let mut gold_subs: std::collections::HashSet<String> = std::collections::HashSet::new();
        for pair in gold["subsumptions"].as_array().expect("subsumptions array") {
            let sub = local(pair[0].as_str().unwrap());
            let sup = local(pair[1].as_str().unwrap());
            gold_universe.insert(sub.clone());
            gold_universe.insert(sup.clone());
            gold_subs.insert(sub.clone());
            gold_pairs.insert((sub, sup));
        }

        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named_set: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let mut tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named_set,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        // subjects = gold-classified (sub-side) names, optionally capped —
        // expressed through the production `queries` mechanism.
        let mut subjects: Vec<usize> = (0..tin.concepts.len())
            .filter(|&i| gold_subs.contains(&tin.concepts[i]))
            .collect();
        if let Some(cap) = std::env::var("KM_BRIDGE_MAX_SUBJECTS")
            .ok()
            .and_then(|s| s.parse::<usize>().ok())
        {
            subjects.truncate(cap);
        }
        let subj_names: std::collections::HashSet<String> =
            subjects.iter().map(|&i| tin.concepts[i].clone()).collect();
        tin.queries = subjects.clone();

        let t0 = std::time::Instant::now();
        let res = bridged_classify(&tin);
        let elapsed = t0.elapsed();
        let Some(r) = res else {
            eprintln!(
                "BRIDGE-CLASSIFY-PROD {path}: DEFERRED after {:.1}s",
                elapsed.as_secs_f64()
            );
            return;
        };
        let mut derived: std::collections::HashSet<(String, String)> =
            std::collections::HashSet::new();
        for &(a, b) in &r.subsumptions {
            let (sub, sup) = (tin.concepts[a].clone(), tin.concepts[b].clone());
            if gold_universe.contains(&sup) {
                derived.insert((sub, sup));
            }
        }
        // unsat subjects subsume-into everything in gold's universe rows;
        // gold encodes them as pairs already, so expand for the diff.
        for &u in &r.unsatisfiable {
            let sub = tin.concepts[u].clone();
            for sup in &gold_universe {
                if *sup != sub {
                    derived.insert((sub.clone(), sup.clone()));
                }
            }
        }
        let gold_restricted: std::collections::HashSet<(String, String)> = gold_pairs
            .iter()
            .filter(|(sub, sup)| subj_names.contains(sub) && gold_universe.contains(sup))
            .cloned()
            .collect();
        for m in gold_restricted.difference(&derived).take(20) {
            eprintln!("MISSING (incomplete): {} ⊑ {}", m.0, m.1);
        }
        for sp in derived.difference(&gold_restricted).take(20) {
            eprintln!("SPURIOUS (unsound): {} ⊑ {}", sp.0, sp.1);
        }
        eprintln!(
            "BRIDGE-CLASSIFY-PROD {path}: subjects={} derived={} gold={} missing={} \
             spurious={} unsat={} elapsed={:.1}s",
            subjects.len(),
            derived.len(),
            gold_restricted.len(),
            gold_restricted.difference(&derived).count(),
            derived.difference(&gold_restricted).count(),
            r.unsatisfiable.len(),
            elapsed.as_secs_f64(),
        );
    }

    /// Singleton-concept merge (the datatype value-identity clause shape
    /// `V(x) ∧ V(y) → x = y`): X has an r-successor forced into `V ⊓ A` and
    /// an s-successor forced into `V ⊓ ¬A` (via `VA2 ⊓ A ⊑ ⊥`). The two
    /// V-carriers are ONE semantic object, so the deterministic
    /// scan-at-fixpoint merge (u02) must unite them and clash `A ⊓ ¬A` ⇒ X
    /// unsatisfiable. Without the merge the graph is clash-free and the
    /// probe under-detects (the earlier state counted the clause unsupported
    /// and DECLINED). Also asserts the clause is CONSUMED (unsupported == 0,
    /// no defer) and that a singleton-free sibling Y stays satisfiable.
    #[test]
    fn singleton_concept_merge_value_identity_unsat() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, c: usize, t: usize| HAtom::Concept { neg, c, t };
        // concepts: 0=X 1=V 2=A 3=VA1 4=VA2 5=Y
        let tin = TInput {
            concepts: vec![
                "X".into(),
                "V".into(),
                "A".into(),
                "VA1".into(),
                "VA2".into(),
                "Y".into(),
            ],
            roles: vec!["r".into(), "s".into()],
            clauses: vec![
                // V(x) ∧ V(y) → x = y  (the singleton / value-identity shape)
                HtClause {
                    body: vec![c(false, 1, 1), c(false, 1, 2)],
                    head: vec![HAtom::Eq { s: 1, t: 2 }],
                },
                // X ⊑ ∃r.VA1 ; X ⊑ ∃s.VA2
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 3,
                        t: 0,
                    }],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 1,
                        neg: false,
                        c: 4,
                        t: 0,
                    }],
                },
                // VA1 ⊑ V ; VA1 ⊑ A ; VA2 ⊑ V ; VA2 ⊓ A ⊑ ⊥
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0), c(false, 2, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let r = bridged_classify(&tin).expect("singleton clause must be CONSUMED (no defer)");
        assert!(
            r.unsatisfiable.contains(&0),
            "X must be UNSAT via the value-identity merge (got unsat={:?})",
            r.unsatisfiable
        );
        assert!(
            !r.unsatisfiable.contains(&5),
            "Y (singleton-free) must stay satisfiable"
        );
    }

    /// Fragment-coverage report on a REAL ontology: set `KM_BRIDGE_ONT` to an
    /// .owl/.ofn path and run with `-- --ignored --nocapture`. Reports how
    /// many TInput clauses the v1 bridge encodes vs counts as unsupported —
    /// the data that prioritises the next bridge wave (absorption, inverse,
    /// cardinality). Diagnostic only; asserts nothing about verdicts.
    #[test]
    #[ignore]
    fn bridge_coverage_report() {
        let path = std::env::var("KM_BRIDGE_ONT").expect("set KM_BRIDGE_ONT=<ont path>");
        let text = std::fs::read_to_string(&path).expect("readable ontology");
        let fr = crate::frontend::ofn_to_clauses(&text).expect("in fragment");
        let named: std::collections::HashSet<String> = fr.named.iter().cloned().collect();
        let tin = crate::orchestrate::cb_to_ht::convert(
            &fr.clauses,
            Some(&fr.rbox),
            &named,
            &fr.cardinalities,
            &fr.definers,
            &fr.source_axioms,
            true,
            &fr.rules,
            false,
        );
        let mut ctx = CalculationAlgorithmContextBase::new();
        ctx.base.used_concept_priority_strategy =
            Some(ConceptProcessingPriorityStrategy::new_concrete_operator());
        let top = {
            let mut c = Concept::new();
            c.set_concept_tag(1);
            c.set_operator_code(op::CCTOP);
            ctx.ontology_arenas_mut().alloc_concept(c)
        };
        ctx.processing_data_box_mut().ontology_top_concept = top;
        let bridged = bridge_tinput(&mut ctx, &tin);
        eprintln!(
            "BRIDGE-COVERAGE {path}: concepts={} roles={} clauses={} encoded_impls={} \
             absorbed={} top_attached={} unsupported={} (inverse={} nominals={} card_defs={} chains={})",
            tin.concepts.len(),
            tin.roles.len(),
            tin.clauses.len(),
            bridged.tbox.len(),
            bridged.absorbed,
            bridged.top_attached,
            bridged.unsupported,
            tin.inverse,
            tin.nominals.len(),
            tin.card_defs.len(),
            tin.chains.len(),
        );
    }

    // -----------------------------------------------------------------------
    // Task #23: saturation-first probe answering.
    //
    // These tests drive `bridged_saturate` DIRECTLY (no env flag — env vars
    // are process-global and the suite runs multi-threaded) and cross-check
    // every certain verdict against the completion-probe classification as
    // the oracle.
    // -----------------------------------------------------------------------

    #[test]
    fn saturation_answers_simple_taxonomy() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B, B ⊑ C — the pure-Horn case saturation must fully answer.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 1, 0)],
                    head: vec![c(false, 2, 0)],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict,
            vec![Some(false); 3],
            "all three classes are satisfiable and must be SAT-certain"
        );
        assert_eq!(out.certain_subsumers[0].as_deref(), Some(&[1usize, 2][..]));
        assert_eq!(out.certain_subsumers[1].as_deref(), Some(&[2usize][..]));
        assert_eq!(out.certain_subsumers[2].as_deref(), Some(&[][..]));
        // Oracle: the probe path derives the same taxonomy.
        let r = bridged_classify(&tin).expect("classify");
        let mut probe_subs = r.subsumptions.clone();
        probe_subs.sort_unstable();
        assert_eq!(probe_subs, vec![(0, 1), (0, 2), (1, 2)]);
        assert!(r.unsatisfiable.is_empty());
    }

    #[test]
    fn saturation_existential_applies_role_domain_before_certifying() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |cc: usize, t: usize| HAtom::Concept {
            neg: false,
            c: cc,
            t,
        };
        // A ⊆ ∃r.T and Domain(r, D) entail A ⊆ D. This is the
        // dominant ore_ont_9663 shape: a saturation row is complete only if
        // the domain consequence is present, otherwise it must remain unknown
        // for the completion probe.
        let tin = TInput {
            concepts: vec!["A".into(), "D".into(), "T".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 2,
                        t: 0,
                    }],
                },
                HtClause {
                    body: vec![HAtom::Role { r: 0, s: 0, t: 1 }],
                    head: vec![c(1, 0)],
                },
            ],
            ..Default::default()
        };

        let oracle = bridged_classify_opts(&tin, false, false).expect("completion oracle");
        assert!(oracle.subsumptions.contains(&(0, 1)));

        let out = bridged_saturate(&tin).expect("in fragment");
        if out.sat_verdict[0] == Some(false) {
            assert!(
                out.certain_subsumers[0]
                    .as_ref()
                    .is_some_and(|subsumers| subsumers.contains(&1)),
                "a SAT-certain A row must include the role-domain subsumer D"
            );
        }
    }

    #[test]
    fn saturation_detects_unsat_concept() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B and A ⊓ B ⊑ ⊥ — the deterministic clash must surface as
        // UNSAT-certain on A while B stays SAT-certain.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 0, 0), c(false, 1, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(out.sat_verdict[0], Some(true), "A is unsatisfiable");
        assert_eq!(out.sat_verdict[1], Some(false), "B is satisfiable");
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
        assert!(!r.unsatisfiable.contains(&1));
    }

    #[test]
    fn probe_oracle_alone_detects_unsat_concept() {
        // DIAGNOSTIC twin of `saturation_detects_unsat_concept` WITHOUT the
        // saturation pre-pass: isolates whether the probe path alone answers
        // the tiny A ⊑ B, A ⊓ B ⊑ ⊥ input (checks the oracle, not saturation).
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 0, 0), c(false, 1, 0)],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let r = bridged_classify(&tin).expect("classify");
        assert!(
            r.unsatisfiable.contains(&0),
            "probe path must detect A unsat (got unsat={:?} subs={:?})",
            r.unsatisfiable,
            r.subsumptions
        );
    }

    #[test]
    fn saturation_defers_disjunction_subjects() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ B ⊔ C — branching: the non-branching saturation must NOT claim
        // a certain verdict built on one disjunct (the OR rule goes critical;
        // with no disjunct entailed the node is insufficient ⇒ unknown).
        // B and C stay plain satisfiable classes.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            clauses: vec![HtClause {
                body: vec![c(false, 0, 0)],
                head: vec![c(false, 1, 0), c(false, 2, 0)],
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        // Soundness bar: whatever A gets, it must not be a WRONG certainty.
        // A is satisfiable with no named subsumers; SAT-certain is acceptable
        // ONLY with an empty subsumer set; unknown (defer) is acceptable.
        match out.sat_verdict[0] {
            Some(true) => panic!("A is satisfiable — UNSAT-certain is unsound"),
            Some(false) => {
                assert_eq!(
                    out.certain_subsumers[0].as_deref(),
                    Some(&[][..]),
                    "a certain subsumer from ONE disjunct branch would be unsound"
                );
            }
            None => {}
        }
        assert_eq!(out.sat_verdict[1], Some(false));
        assert_eq!(out.sat_verdict[2], Some(false));
    }

    #[test]
    fn saturation_never_sat_certain_on_forall_exists_clash() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // A ⊑ ∃r.B and A ⊑ ∀r.¬B ⇒ A unsatisfiable. The cheap saturation
        // shares successor nodes, so it may not DETECT the clash — but it must
        // never claim SAT-certain (the ∀-into-creation-direction escape hatch:
        // criticality/insufficiency must fire).
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 1,
                        t: 0,
                    }],
                },
                // A(x) ∧ r(x,y) ∧ B(y) → ⊥  (A ⊑ ∀r.¬B)
                HtClause {
                    body: vec![
                        c(false, 0, 0),
                        HAtom::Role { r: 0, s: 0, t: 1 },
                        c(false, 1, 1),
                    ],
                    head: vec![],
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT — SAT-certain would be a soundness bug \
             (the ∀-into-creation-direction hatch must defer or clash)"
        );
        assert_eq!(out.sat_verdict[1], Some(false), "B alone is satisfiable");
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
    }

    // -----------------------------------------------------------------------
    // Task #24: precise ATMOST criticality test (isCriticalATMOSTConcept-
    // DescriptorInsufficient + collect + simple/detailed mergeability).
    // -----------------------------------------------------------------------

    /// `A ⊑ ∃r.B, A ⊑ ≤2 r.B`: one successor against a bound of two — the
    /// precise test must answer SAT-certain (the old conservative stub
    /// deferred EVERY critical ≤n).
    #[test]
    fn saturation_answers_atmost_within_bound() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![HtClause {
                body: vec![c(false, 0, 0)],
                head: vec![HAtom::Exist {
                    r: 0,
                    neg: false,
                    c: 1,
                    t: 0,
                }],
            }],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 2,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "A has 1 r.B successor against ≤2 r.B — must be SAT-certain"
        );
        assert_eq!(out.sat_verdict[1], Some(false));
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// `A ⊑ ∃r.B, A ⊑ ∃r.C, A ⊑ ≤1 r.B`: the C-successor does not count
    /// toward the qualified bound (its label cannot positively satisfy B) —
    /// SAT-certain with the precise qualified counting.
    #[test]
    fn saturation_atmost_qualified_counting_sat() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 1)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
            ],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "only the B-successor counts toward ≤1 r.B — A is SAT-certain"
        );
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// `A ⊑ ∃r.B1, A ⊑ ∃r.B2, B1 ⊑ B, B2 ⊑ B, A ⊑ ≤1 r.B`: both successors
    /// count, but their labels are compatible — the mergeability discount
    /// brings the residual cardinality back to the bound ⇒ SAT-certain.
    #[test]
    fn saturation_atmost_merging_discount_sat() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "B1".into(), "B2".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 3)],
                },
                HtClause {
                    body: vec![c(false, 2, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
            ],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_eq!(
            out.sat_verdict[0],
            Some(false),
            "the two r-successors are label-mergeable — ≤1 r.B holds, A SAT-certain"
        );
        // Oracle agreement.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.is_empty());
    }

    /// The disjoint twin of the merging-discount case: `B1 ⊓ B2 ⊑ ⊥` makes
    /// the merge clash, so A is UNSATISFIABLE — the saturation must NOT
    /// claim SAT-certain (label-merging-problematic must veto the discount).
    #[test]
    fn saturation_atmost_disjoint_successors_not_sat_certain() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        let ex = |r: usize, cc: usize| HAtom::Exist {
            r,
            neg: false,
            c: cc,
            t: 0,
        };
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "B1".into(), "B2".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 2)],
                },
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![ex(0, 3)],
                },
                HtClause {
                    body: vec![c(false, 2, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0)],
                },
                // B1 ⊓ B2 ⊑ ⊥
                HtClause {
                    body: vec![c(false, 2, 0), c(false, 3, 0)],
                    head: vec![],
                },
            ],
            card_defs: vec![CardDefJson {
                marker: 0,
                min: false,
                n: 1,
                role: 0,
                filler: 1,
            }],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT (disjoint successors under ≤1 r.B) — SAT-certain would \
             mean the mergeability discount ignored the disjointness"
        );
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(r.unsatisfiable.contains(&0));
    }

    /// `A ⊑ ≥3 r.B, A ⊑ ≤2 r.B`: the pairwise-distinct ≥3 successors exceed
    /// the bound — the saturation must not read SAT-certain (Konclude clashes
    /// the node in collectATMOSTConceptRelevantSuccessors when a single
    /// distinct-successor block already exceeds the allowance).
    #[test]
    fn saturation_atleast_over_atmost_not_sat_certain() {
        use crate::orchestrate::cb_to_ht::{CardDefJson, HAtom, HtClause, TInput};
        let tin = TInput {
            concepts: vec!["A".into(), "B".into()],
            roles: vec!["r".into()],
            clauses: vec![],
            card_defs: vec![
                CardDefJson {
                    marker: 0,
                    min: true,
                    n: 3,
                    role: 0,
                    filler: 1,
                },
                CardDefJson {
                    marker: 0,
                    min: false,
                    n: 2,
                    role: 0,
                    filler: 1,
                },
            ],
            ..Default::default()
        };
        let out = bridged_saturate(&tin).expect("in fragment");
        assert_ne!(
            out.sat_verdict[0],
            Some(false),
            "A is UNSAT (≥3 r.B vs ≤2 r.B) — SAT-certain is unsound"
        );
        assert_eq!(out.sat_verdict[1], Some(false), "B alone is satisfiable");
        // Oracle: the probe path proves A unsatisfiable.
        let r = bridged_classify(&tin).expect("classify");
        assert!(
            r.unsatisfiable.contains(&0),
            "probe oracle must prove A unsat (got {:?})",
            r.unsatisfiable
        );
    }

    // -----------------------------------------------------------------------
    // Saturation-node coupling into the completion probes (task #24 wave 2):
    // expand-from-saturation (u17) + caching-blocking (u22) armed inside the
    // probe env after a same-env saturation pass. Driven programmatically
    // (env-var-independent).
    // -----------------------------------------------------------------------

    /// The ∃-rule must replay the filler's saturated label onto the fresh
    /// successor (expansion) and establish saturation blocking on it — and
    /// both must KEEP firing after a `reset_probe_env` carry (the arenas +
    /// reference linkings survive the reset).
    #[test]
    fn satcache_expansion_and_blocking_fire_in_probe() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B))\n\
             Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert_eq!(bridged.unsupported, 0, "fully bridged");
        assert!(
            run_bridged_saturation(&mut ctx, &bridged),
            "saturation within budget"
        );
        let arm = |algo: &mut CompletionTaskHandleAlgorithm| {
            configure_production_completion_saturation_coupling(algo);
        };
        arm(&mut algo);
        assert!(
            !algo.conf_successor_saturation_expansion_restrictions_resolving,
            "production completion must match Konclude's disabled restriction resolver"
        );
        assert!(
            algo.conf_saturation_expansion_cache_reading,
            "production coupling must retain cached successors after modification"
        );
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        let (a, d) = (bridged.named[idx("A")], bridged.named[idx("D")]);
        let mut id = 0i64;
        // A ⊓ ¬D is satisfiable (A ⋢ D); the drive expands A's ∃r.B.
        let verdict = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id,
            &[(a, false), (d, true)],
        );
        assert_eq!(verdict, Some(false), "A ⊑ D must NOT hold");
        assert!(
            algo.saturation_expansion_concept_count > 0,
            "the saturated filler label must be replayed onto the ∃-successor"
        );
        assert!(
            algo.saturation_cache_establish_count > 0,
            "the ∃-successor must be established saturation-blocked"
        );
        // The classify-style reset must CARRY the saturation state: the
        // coupling keeps firing on the warm env.
        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        arm(&mut algo);
        let mut id2 = 0i64;
        let warm = bridged_unsat(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut id2,
            &[(a, false), (d, true)],
        );
        assert_eq!(warm, Some(false), "verdict stable across the carry");
        assert!(
            algo.saturation_expansion_concept_count > 0
                && algo.saturation_cache_establish_count > 0,
            "the coupling must survive reset_probe_env (saturation arenas carried)"
        );
    }

    #[test]
    fn satcache_successful_root_writes_and_preserves_associated_expansion() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n)"
        );
        let env = bridge_ofn(&ofn);
        let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
        assert!(run_bridged_saturation(&mut ctx, &bridged));
        install_bridge_saturation_node_expansion_cache(&mut ctx);
        configure_production_search(&mut algo);
        algo.conf_expand_created_successors_from_saturation = true;
        algo.conf_caching_blocking_from_saturation = true;
        algo.conf_saturation_satisfiabilitiy_expansion_cache_writing = true;
        let a = env
            .tin
            .concepts
            .iter()
            .position(|name| name == "A")
            .expect("A in classification input");
        // Production probes reserve low IDs for ontology individuals.
        let mut next_id = 1_000;
        assert!(bridged_classify_subject(
            &mut algo,
            &mut ctx,
            &bridged,
            &mut next_id,
            a,
            bridged.named.len(),
        )
        .is_some());
        let state = ctx
            .take_used_saturation_node_expansion_cache_handler()
            .expect("associated-expansion cache remains installed");
        assert!(
            state.cache_context.sat_expansion_cache_entries.len() > 0,
            "successful root must write an associated-expansion cache entry"
        );
        ctx.restore_used_saturation_node_expansion_cache_handler(state);

        reset_probe_env(&mut algo, &mut ctx, &bridged, true);
        assert!(
            ctx.take_used_saturation_node_expansion_cache_handler()
                .is_some(),
            "classification reset must preserve the ontology-wide cache"
        );
    }

    /// A clashed saturation node must replay as a CLASH in the probe: with
    /// B deterministically unsatisfiable (B ⊑ C ⊓ ¬C), probing A (⊑ ∃r.B)
    /// must answer UNSAT through `try_expansion_from_saturated_data`'s
    /// clash arm — and agree with the plain (uncoupled) probe.
    #[test]
    fn satcache_clash_replay_probe_unsat() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:A ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:B ObjectComplementOf(:C))\n)"
        );
        let env = bridge_ofn(&ofn);
        let idx = |s: &str| -> usize {
            env.tin
                .concepts
                .iter()
                .position(|n| n == s)
                .unwrap_or_else(|| panic!("concept {s} not in TInput"))
        };
        // Plain probe (no saturation, no coupling): A unsat.
        {
            let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
            assert_eq!(bridged.unsupported, 0);
            let a = bridged.named[idx("A")];
            let mut id = 0i64;
            let plain = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false)]);
            assert_eq!(plain, Some(true), "A is unsatisfiable (plain probe)");
        }
        // Coupled probe: the ∃-rule must clash from B's CLASHED saturation node.
        {
            let (mut algo, mut ctx, bridged) = fresh_bridge_env(&env.tin);
            assert!(run_bridged_saturation(&mut ctx, &bridged));
            algo.conf_expand_created_successors_from_saturation = true;
            algo.conf_caching_blocking_from_saturation = true;
            let a = bridged.named[idx("A")];
            let mut id = 0i64;
            let coupled = bridged_unsat(&mut algo, &mut ctx, &bridged, &mut id, &[(a, false)]);
            assert_eq!(coupled, Some(true), "A is unsatisfiable (coupled probe)");
        }
    }

    /// Public-API A/B/C: plain probes vs saturation-only vs saturation +
    /// coupling must classify identically on a mixed ontology whose
    /// disjunction forces a probe residue (the coupling actually runs).
    #[test]
    fn satcache_classification_matches_plain() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y)) Declaration(Class(:Z))\n\
             Declaration(Class(:A1)) Declaration(Class(:A2))\n\
             Declaration(Class(:B)) Declaration(Class(:C))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:X ObjectUnionOf(:A1 :A2))\n\
             SubClassOf(:A1 :Y)\n\
             SubClassOf(:A2 :Y)\n\
             SubClassOf(:Y ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:Z ObjectAllValuesFrom(:r ObjectComplementOf(:B)))\n)"
        );
        let env = bridge_ofn(&ofn);
        let norm = |r: BridgedClassification| {
            let mut u = r.unsatisfiable;
            let mut s = r.subsumptions;
            u.sort_unstable();
            s.sort_unstable();
            (u, s)
        };
        let plain = norm(bridged_classify_opts(&env.tin, false, false).expect("plain arm"));
        let sat_only = norm(bridged_classify_opts(&env.tin, true, false).expect("sat-only arm"));
        let coupled = norm(bridged_classify_opts(&env.tin, true, true).expect("coupled arm"));
        assert_eq!(plain, sat_only, "saturation-only must not change verdicts");
        assert_eq!(
            plain, coupled,
            "the saturation-node coupling must not change verdicts"
        );
    }

    /// Horn ∃-cycle equality: `B ⊑ ∃r.B` grows an unbounded chain that the
    /// coupled arm must terminate via successor absorption (the cached
    /// successor's generating ∃ is absorbed instead of expanded) with the
    /// SAME classification as the plain arm (which terminates via blocking).
    /// Horn-only so every read-off is authoritative — no branch probes, no
    /// poison-defer noise in either arm.
    #[test]
    fn satcache_absorption_terminates_exists_cycle() {
        let ofn = format!(
            "{PREFIX}\
             Declaration(Class(:X)) Declaration(Class(:Y))\n\
             Declaration(Class(:B)) Declaration(Class(:C)) Declaration(Class(:D))\n\
             Declaration(ObjectProperty(:r))\n\
             SubClassOf(:X :Y)\n\
             SubClassOf(:Y ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:B :C)\n\
             SubClassOf(:B ObjectSomeValuesFrom(:r :B))\n\
             SubClassOf(:C :D)\n)"
        );
        let env = bridge_ofn(&ofn);
        let norm = |r: BridgedClassification| {
            let mut u = r.unsatisfiable;
            let mut s = r.subsumptions;
            u.sort_unstable();
            s.sort_unstable();
            (u, s)
        };
        let plain = norm(bridged_classify_opts(&env.tin, false, false).expect("plain arm"));
        let coupled = norm(bridged_classify_opts(&env.tin, true, true).expect("coupled arm"));
        assert_eq!(
            plain, coupled,
            "absorption must preserve the classification"
        );
        assert!(
            plain.1.len() >= 4,
            "sanity: the taxonomy has X⊑Y, B⊑C, B⊑D, C⊑D (got {:?})",
            plain.1
        );
    }

    /// Full-agreement harness: saturation certainties vs the probe-path
    /// classification on a small mixed ontology (Horn taxonomy + one
    /// disjunction + one ∃/∀ interaction). Every CERTAIN saturation answer
    /// must match the oracle exactly; unknowns are free.
    #[test]
    fn saturation_certainties_agree_with_probe_classification() {
        use crate::orchestrate::cb_to_ht::{HAtom, HtClause, TInput};
        let c = |neg: bool, cc: usize, t: usize| HAtom::Concept { neg, c: cc, t };
        // 0=A 1=B 2=C 3=D 4=E; r
        // A ⊑ B, B ⊑ C, D ⊑ B ⊔ C, E ⊑ ∃r.A, E ⊑ ∀r.B (entailed anyway), C ⊓ A ⊑ D? no — keep simple.
        let tin = TInput {
            concepts: vec!["A".into(), "B".into(), "C".into(), "D".into(), "E".into()],
            roles: vec!["r".into()],
            clauses: vec![
                HtClause {
                    body: vec![c(false, 0, 0)],
                    head: vec![c(false, 1, 0)],
                },
                HtClause {
                    body: vec![c(false, 1, 0)],
                    head: vec![c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 3, 0)],
                    head: vec![c(false, 1, 0), c(false, 2, 0)],
                },
                HtClause {
                    body: vec![c(false, 4, 0)],
                    head: vec![HAtom::Exist {
                        r: 0,
                        neg: false,
                        c: 0,
                        t: 0,
                    }],
                },
            ],
            ..Default::default()
        };
        let oracle = bridged_classify(&tin).expect("classify");
        let oracle_subs: std::collections::HashSet<(usize, usize)> =
            oracle.subsumptions.iter().copied().collect();
        let out = bridged_saturate(&tin).expect("in fragment");
        for i in 0..tin.concepts.len() {
            match out.sat_verdict[i] {
                Some(true) => assert!(
                    oracle.unsatisfiable.contains(&i),
                    "saturation UNSAT-certain on {} disagrees with oracle",
                    tin.concepts[i]
                ),
                Some(false) => {
                    assert!(
                        !oracle.unsatisfiable.contains(&i),
                        "saturation SAT-certain on {} but oracle says unsat",
                        tin.concepts[i]
                    );
                    if let Some(subs) = &out.certain_subsumers[i] {
                        let sat_set: std::collections::HashSet<(usize, usize)> =
                            subs.iter().map(|&cc| (i, cc)).collect();
                        let oracle_row: std::collections::HashSet<(usize, usize)> = oracle_subs
                            .iter()
                            .filter(|&&(s, _)| s == i)
                            .copied()
                            .collect();
                        assert_eq!(
                            sat_set, oracle_row,
                            "certain-subsumer row for {} diverges from oracle",
                            tin.concepts[i]
                        );
                    }
                }
                None => {}
            }
        }
    }
}
