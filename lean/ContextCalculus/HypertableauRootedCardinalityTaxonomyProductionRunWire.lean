import ContextCalculus.HypertableauCardinalityDoublingTraceWire
import ContextCalculus.HypertableauNativeABoxCardinalityTaxonomyWire
import ContextCalculus.HypertableauRootedOrdinaryTaxonomyProductionRunWire

/-!
# Complete rooted native-ABox cardinality taxonomy production runs

This wire binds a semantically checked cardinality taxonomy cell to every
rooted, state-bearing cardinality frontier traversed by its production run.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRootedCardinalityTaxonomyProductionRun where
  version : Nat
  start_budget : Nat
  root_count : Nat
  max_width : Nat
  frontiers : List WireRootedCardinalityAddressRefinementDocument
  terminal : WireNativeABoxCardinalityTaxonomyDecision
deriving FromJson, ToJson, Repr

def WireNativeABoxCardinalityTaxonomyDecision.nodeCount
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.node_count
  | .unsat initial _ _ _ => initial.node_count

def WireNativeABoxCardinalityTaxonomyDecision.variableCount
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.variable_count
  | .unsat initial _ _ _ => initial.variable_count

def WireNativeABoxCardinalityTaxonomyDecision.conceptCount
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.concepts.length
  | .unsat initial _ _ _ => initial.abox.concepts.length

def WireNativeABoxCardinalityTaxonomyDecision.roleCount
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.roles.length
  | .unsat initial _ _ _ => initial.abox.roles.length

def WireNativeABoxCardinalityTaxonomyDecision.rootCount
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.individuals.length + 1
  | .unsat initial _ _ _ => initial.abox.individuals.length + 1

def WireNativeABoxCardinalityTaxonomyDecision.ontology
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : List WireClause :=
  match wire.evidence with
  | .sat certificate => certificate.seed.ontology
  | .unsat initial _ _ _ => initial.ontology

def WireNativeABoxCardinalityTaxonomyDecision.definitions
    (wire : WireNativeABoxCardinalityTaxonomyDecision) : List WireCardinalityDef :=
  match wire.evidence with
  | .sat certificate => certificate.definitions
  | .unsat _ definitions _ _ => definitions

def WireEqState.containsLabel (state : WireEqState)
    (node conceptId : Nat) (neg : Bool) : Bool :=
  state.labels.any fun label =>
    label.node == node && label.literal.concept == conceptId &&
      label.literal.neg == neg

def WireNativeABoxTaxonomyQuery.presentInEq
    (query : WireNativeABoxTaxonomyQuery) (state : WireEqState) : Bool :=
  match query with
  | WireNativeABoxTaxonomyQuery.concept root conceptId =>
      state.containsLabel root conceptId false
  | WireNativeABoxTaxonomyQuery.subsumption root sub sup =>
      state.containsLabel root sub false && state.containsLabel root sup true

def WireRootedCardinalityTaxonomyProductionRun.trace
    (wire : WireRootedCardinalityTaxonomyProductionRun) :
    WireRootedCardinalityDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  root_count := wire.root_count
  max_width := wire.max_width
  frontiers := wire.frontiers
}

def WireRootedCardinalityTaxonomyProductionRun.matchesLast
    (wire : WireRootedCardinalityTaxonomyProductionRun) : Bool :=
  match wire.frontiers.getLast? with
  | none => decide (wire.terminal.rootCount = wire.root_count)
  | some frontier =>
      frontier.variable_count == wire.terminal.variableCount &&
      frontier.frontier.root_count == wire.terminal.rootCount &&
      frontier.frontier.root_count == wire.root_count &&
      frontier.frontier.concept_count == wire.terminal.conceptCount &&
      frontier.frontier.role_count == wire.terminal.roleCount &&
      frontier.frontier.definition_count == wire.terminal.definitions.length &&
      frontier.frontier.max_width == wire.max_width &&
      wire.terminal.query.presentInEq frontier.runtime.state.base &&
      toJson frontier.ontology == toJson wire.terminal.ontology &&
      toJson frontier.definitions == toJson wire.terminal.definitions

def WireRootedCardinalityTaxonomyProductionRun.terminalAccepted
    (wire : WireRootedCardinalityTaxonomyProductionRun) : Bool :=
  match wire.terminal.check with
  | .ok true =>
      decide (wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      wire.matchesLast
  | _ => false

def WireRootedCardinalityTaxonomyProductionRun.check
    (wire : WireRootedCardinalityTaxonomyProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireRootedCardinalityTaxonomyProductionRun.Accepted
    (wire : WireRootedCardinalityTaxonomyProductionRun) : Prop where
  trace : WireRootedCardinalityDoublingTrace.ValidFrom wire.start_budget
    wire.root_count wire.max_width wire.frontiers
  terminal : wire.terminal.check = .ok true
  withinBudget : wire.terminal.nodeCount ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  sameProblem : wire.matchesLast = true

theorem WireRootedCardinalityTaxonomyProductionRun.terminalAccepted_sound
    (wire : WireRootedCardinalityTaxonomyProductionRun)
    (hcheck : wire.terminalAccepted = true) :
    wire.terminal.check = .ok true ∧
      wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      wire.matchesLast = true := by
  unfold WireRootedCardinalityTaxonomyProductionRun.terminalAccepted at hcheck
  cases hterminal : wire.terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireRootedCardinalityTaxonomyProductionRun.check_sound
    (wire : WireRootedCardinalityTaxonomyProductionRun)
    (hcheck : wire.check = true) : wire.Accepted := by
  simp only [WireRootedCardinalityTaxonomyProductionRun.check,
    Bool.and_eq_true] at hcheck
  have hterminal := wire.terminalAccepted_sound hcheck.2
  exact ⟨wire.trace.check_sound hcheck.1.2, hterminal.1,
    hterminal.2.1, hterminal.2.2⟩

theorem WireRootedCardinalityTaxonomyProductionRun.Accepted.terminal_semantics
    {wire : WireRootedCardinalityTaxonomyProductionRun} (accepted : wire.Accepted) :
    ∃ decoded : DecodedNativeABoxCardinalityTaxonomyDecision,
      wire.terminal.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  have hterminal := accepted.terminal
  unfold WireNativeABoxCardinalityTaxonomyDecision.check at hterminal
  cases hdecode : wire.terminal.decode with
  | error message => simp [hdecode] at hterminal
  | ok decoded => exact ⟨decoded, rfl, decoded.semantic_valid⟩

#print axioms WireRootedCardinalityTaxonomyProductionRun.check_sound
#print axioms WireRootedCardinalityTaxonomyProductionRun.Accepted.terminal_semantics

end ContextCalculus.Hypertableau
