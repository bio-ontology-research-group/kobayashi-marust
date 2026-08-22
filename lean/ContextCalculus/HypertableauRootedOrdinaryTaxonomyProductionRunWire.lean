import ContextCalculus.HypertableauDoublingTraceWire
import ContextCalculus.HypertableauNativeABoxTaxonomyWire

/-!
# Complete rooted native-ABox ordinary taxonomy production runs

This wire binds one semantically checked native-ABox taxonomy cell to every
ordinary frontier traversed by the equality-aware production run that decided
that exact query.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRootedOrdinaryTaxonomyProductionRun where
  version : Nat
  start_budget : Nat
  root_count : Nat
  frontiers : List WireAddressRefinementDocument
  terminal : WireNativeABoxTaxonomyDecision
deriving FromJson, ToJson, Repr

def WireNativeABoxTaxonomyDecision.nodeCount
    (wire : WireNativeABoxTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.node_count
  | .unsat initial _ => initial.node_count

def WireNativeABoxTaxonomyDecision.variableCount
    (wire : WireNativeABoxTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.variable_count
  | .unsat initial _ => initial.variable_count

def WireNativeABoxTaxonomyDecision.conceptCount
    (wire : WireNativeABoxTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.concepts.length
  | .unsat initial _ => initial.abox.concepts.length

def WireNativeABoxTaxonomyDecision.roleCount
    (wire : WireNativeABoxTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.roles.length
  | .unsat initial _ => initial.abox.roles.length

def WireNativeABoxTaxonomyDecision.rootCount
    (wire : WireNativeABoxTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.individuals.length + 1
  | .unsat initial _ => initial.abox.individuals.length + 1

def WireNativeABoxTaxonomyDecision.ontology
    (wire : WireNativeABoxTaxonomyDecision) : List WireClause :=
  match wire.evidence with
  | .sat certificate => certificate.seed.ontology
  | .unsat initial _ => initial.ontology

def WireCertificate.containsLabel (state : WireCertificate)
    (node concept : Nat) (neg : Bool) : Bool :=
  state.labels.any fun label =>
    label.node == node && label.literal.concept == concept &&
      label.literal.neg == neg

def WireNativeABoxTaxonomyQuery.presentIn
    (query : WireNativeABoxTaxonomyQuery) (state : WireCertificate) : Bool :=
  match query with
  | WireNativeABoxTaxonomyQuery.concept root conceptId =>
      state.containsLabel root conceptId false
  | WireNativeABoxTaxonomyQuery.subsumption root sub sup =>
      state.containsLabel root sub false && state.containsLabel root sup true

def WireRootedOrdinaryTaxonomyProductionRun.trace
    (wire : WireRootedOrdinaryTaxonomyProductionRun) : WireAddressDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  frontiers := wire.frontiers
}

def WireRootedOrdinaryTaxonomyProductionRun.matchesLast
    (wire : WireRootedOrdinaryTaxonomyProductionRun) : Bool :=
  decide (wire.terminal.rootCount = wire.root_count) &&
  match wire.frontiers.getLast? with
  | none => true
  | some frontier =>
      frontier.state.variable_count == wire.terminal.variableCount &&
      frontier.state.concept_count == wire.terminal.conceptCount &&
      frontier.state.role_count == wire.terminal.roleCount &&
      wire.terminal.query.presentIn frontier.state &&
      toJson frontier.state.ontology == toJson wire.terminal.ontology

def WireRootedOrdinaryTaxonomyProductionRun.terminalAccepted
    (wire : WireRootedOrdinaryTaxonomyProductionRun) : Bool :=
  match wire.terminal.check with
  | .ok true =>
      decide (wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      wire.matchesLast
  | _ => false

def WireRootedOrdinaryTaxonomyProductionRun.check
    (wire : WireRootedOrdinaryTaxonomyProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireRootedOrdinaryTaxonomyProductionRun.Accepted
    (wire : WireRootedOrdinaryTaxonomyProductionRun) : Prop where
  trace : WireAddressDoublingTrace.ValidFrom wire.start_budget wire.frontiers
  terminal : wire.terminal.check = .ok true
  withinBudget : wire.terminal.nodeCount ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  sameProblem : wire.matchesLast = true

theorem WireRootedOrdinaryTaxonomyProductionRun.terminalAccepted_sound
    (wire : WireRootedOrdinaryTaxonomyProductionRun)
    (hcheck : wire.terminalAccepted = true) :
    wire.terminal.check = .ok true ∧
      wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      wire.matchesLast = true := by
  unfold WireRootedOrdinaryTaxonomyProductionRun.terminalAccepted at hcheck
  cases hterminal : wire.terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireRootedOrdinaryTaxonomyProductionRun.check_sound
    (wire : WireRootedOrdinaryTaxonomyProductionRun)
    (hcheck : wire.check = true) : wire.Accepted := by
  simp only [WireRootedOrdinaryTaxonomyProductionRun.check,
    Bool.and_eq_true] at hcheck
  have hterminal := wire.terminalAccepted_sound hcheck.2
  exact ⟨wire.trace.check_sound hcheck.1.2, hterminal.1,
    hterminal.2.1, hterminal.2.2⟩

theorem WireRootedOrdinaryTaxonomyProductionRun.Accepted.terminal_semantics
    {wire : WireRootedOrdinaryTaxonomyProductionRun} (accepted : wire.Accepted) :
    ∃ decoded : DecodedNativeABoxTaxonomyDecision,
      wire.terminal.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  have hterminal := accepted.terminal
  unfold WireNativeABoxTaxonomyDecision.check at hterminal
  cases hdecode : wire.terminal.decode with
  | error message => simp [hdecode] at hterminal
  | ok decoded => exact ⟨decoded, rfl, decoded.semantic_valid⟩

#print axioms WireRootedOrdinaryTaxonomyProductionRun.check_sound
#print axioms WireRootedOrdinaryTaxonomyProductionRun.Accepted.terminal_semantics

end ContextCalculus.Hypertableau
