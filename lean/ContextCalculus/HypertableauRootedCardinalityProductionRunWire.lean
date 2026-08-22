import ContextCalculus.HypertableauCardinalityDoublingTraceWire
import ContextCalculus.HypertableauNativeABoxModelWire

/-!
# Complete rooted native-ABox cardinality production runs

This binds the joint native-ABox SAT or UNSAT terminal to every state-bearing
rooted cardinality frontier traversed by the same production run.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRootedCardinalityProductionRun where
  version : Nat
  start_budget : Nat
  root_count : Nat
  max_width : Nat
  frontiers : List WireRootedCardinalityAddressRefinementDocument
  terminal : WireNativeABoxCardinalityDecisionCertificate
deriving FromJson, ToJson, Repr

def WireNativeABoxCardinalityDecisionCertificate.nodeCount
    (wire : WireNativeABoxCardinalityDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.node_count
  | .unsat refutation => refutation.initial.node_count

def WireNativeABoxCardinalityDecisionCertificate.variableCount
    (wire : WireNativeABoxCardinalityDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.variable_count
  | .unsat refutation => refutation.initial.variable_count

def WireNativeABoxCardinalityDecisionCertificate.conceptCount
    (wire : WireNativeABoxCardinalityDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.concepts.length
  | .unsat refutation => refutation.initial.abox.concepts.length

def WireNativeABoxCardinalityDecisionCertificate.roleCount
    (wire : WireNativeABoxCardinalityDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.roles.length
  | .unsat refutation => refutation.initial.abox.roles.length

def WireNativeABoxCardinalityDecisionCertificate.rootCount
    (wire : WireNativeABoxCardinalityDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.individuals.length + 1
  | .unsat refutation => refutation.initial.abox.individuals.length + 1

def WireNativeABoxCardinalityDecisionCertificate.ontology
    (wire : WireNativeABoxCardinalityDecisionCertificate) : List WireClause :=
  match wire.evidence with
  | .sat certificate => certificate.seed.ontology
  | .unsat refutation => refutation.initial.ontology

def WireNativeABoxCardinalityDecisionCertificate.definitions
    (wire : WireNativeABoxCardinalityDecisionCertificate) : List WireCardinalityDef :=
  match wire.evidence with
  | .sat certificate => certificate.definitions
  | .unsat refutation => refutation.definitions

def WireRootedCardinalityProductionRun.trace
    (wire : WireRootedCardinalityProductionRun) :
    WireRootedCardinalityDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  root_count := wire.root_count
  max_width := wire.max_width
  frontiers := wire.frontiers
}

def WireRootedCardinalityProductionRun.matchesLast
    (wire : WireRootedCardinalityProductionRun) : Bool :=
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
      toJson frontier.ontology == toJson wire.terminal.ontology &&
      toJson frontier.definitions == toJson wire.terminal.definitions

def WireRootedCardinalityProductionRun.terminalAccepted
    (wire : WireRootedCardinalityProductionRun) : Bool :=
  match wire.terminal.check with
  | .ok true =>
      decide (wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      wire.matchesLast
  | _ => false

def WireRootedCardinalityProductionRun.check
    (wire : WireRootedCardinalityProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireRootedCardinalityProductionRun.Accepted
    (wire : WireRootedCardinalityProductionRun) : Prop where
  trace : WireRootedCardinalityDoublingTrace.ValidFrom wire.start_budget
    wire.root_count wire.max_width wire.frontiers
  terminal : wire.terminal.check = .ok true
  withinBudget : wire.terminal.nodeCount ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  sameProblem : wire.matchesLast = true

theorem WireRootedCardinalityProductionRun.terminalAccepted_sound
    (wire : WireRootedCardinalityProductionRun)
    (hcheck : wire.terminalAccepted = true) :
    wire.terminal.check = .ok true ∧
      wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      wire.matchesLast = true := by
  unfold WireRootedCardinalityProductionRun.terminalAccepted at hcheck
  cases hterminal : wire.terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireRootedCardinalityProductionRun.Accepted.terminal_semantics
    {wire : WireRootedCardinalityProductionRun} (accepted : wire.Accepted) :
    ∃ decoded : DecodedNativeABoxCardinalityDecision,
      wire.terminal.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  have hterminal := accepted.terminal
  unfold WireNativeABoxCardinalityDecisionCertificate.check at hterminal
  cases hdecode : wire.terminal.decode with
  | error message => simp [hdecode] at hterminal
  | ok decoded => exact ⟨decoded, rfl, decoded.semantic_valid⟩

theorem WireRootedCardinalityProductionRun.check_sound
    (wire : WireRootedCardinalityProductionRun) (hcheck : wire.check = true) :
    wire.Accepted := by
  simp only [WireRootedCardinalityProductionRun.check, Bool.and_eq_true] at hcheck
  have htrace := wire.trace.check_sound hcheck.1.2
  have hterminal := wire.terminalAccepted_sound hcheck.2
  exact ⟨htrace, hterminal.1, hterminal.2.1, hterminal.2.2⟩

#print axioms WireRootedCardinalityProductionRun.check_sound
#print axioms WireRootedCardinalityProductionRun.Accepted.terminal_semantics

end ContextCalculus.Hypertableau
