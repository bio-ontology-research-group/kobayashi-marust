import ContextCalculus.HypertableauDoublingTraceWire
import ContextCalculus.HypertableauNativeABoxModelWire

/-!
# Complete rooted native-ABox ordinary production runs

This wire binds a joint native-ABox SAT or UNSAT terminal to every
state-bearing ordinary frontier traversed by the same equality-aware run.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRootedOrdinaryProductionRun where
  version : Nat
  start_budget : Nat
  root_count : Nat
  frontiers : List WireAddressRefinementDocument
  terminal : WireNativeABoxDecisionCertificate
deriving FromJson, ToJson, Repr

def WireNativeABoxDecisionCertificate.nodeCount
    (wire : WireNativeABoxDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.node_count
  | .unsat refutation => refutation.initial.node_count

def WireNativeABoxDecisionCertificate.variableCount
    (wire : WireNativeABoxDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.variable_count
  | .unsat refutation => refutation.initial.variable_count

def WireNativeABoxDecisionCertificate.conceptCount
    (wire : WireNativeABoxDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.concepts.length
  | .unsat refutation => refutation.initial.abox.concepts.length

def WireNativeABoxDecisionCertificate.roleCount
    (wire : WireNativeABoxDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.roles.length
  | .unsat refutation => refutation.initial.abox.roles.length

def WireNativeABoxDecisionCertificate.rootCount
    (wire : WireNativeABoxDecisionCertificate) : Nat :=
  match wire.evidence with
  | .sat certificate => certificate.seed.abox.individuals.length + 1
  | .unsat refutation => refutation.initial.abox.individuals.length + 1

def WireNativeABoxDecisionCertificate.ontology
    (wire : WireNativeABoxDecisionCertificate) : List WireClause :=
  match wire.evidence with
  | .sat certificate => certificate.seed.ontology
  | .unsat refutation => refutation.initial.ontology

def WireRootedOrdinaryProductionRun.trace
    (wire : WireRootedOrdinaryProductionRun) : WireAddressDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  frontiers := wire.frontiers
}

def WireRootedOrdinaryProductionRun.matchesLast
    (wire : WireRootedOrdinaryProductionRun) : Bool :=
  decide (wire.terminal.rootCount = wire.root_count) &&
  match wire.frontiers.getLast? with
  | none => true
  | some frontier =>
      frontier.state.variable_count == wire.terminal.variableCount &&
      frontier.state.concept_count == wire.terminal.conceptCount &&
      frontier.state.role_count == wire.terminal.roleCount &&
      toJson frontier.state.ontology == toJson wire.terminal.ontology

def WireRootedOrdinaryProductionRun.terminalAccepted
    (wire : WireRootedOrdinaryProductionRun) : Bool :=
  match wire.terminal.check with
  | .ok true =>
      decide (wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      wire.matchesLast
  | _ => false

def WireRootedOrdinaryProductionRun.check
    (wire : WireRootedOrdinaryProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireRootedOrdinaryProductionRun.Accepted
    (wire : WireRootedOrdinaryProductionRun) : Prop where
  trace : WireAddressDoublingTrace.ValidFrom wire.start_budget wire.frontiers
  terminal : wire.terminal.check = .ok true
  withinBudget : wire.terminal.nodeCount ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  sameProblem : wire.matchesLast = true

theorem WireRootedOrdinaryProductionRun.terminalAccepted_sound
    (wire : WireRootedOrdinaryProductionRun)
    (hcheck : wire.terminalAccepted = true) :
    wire.terminal.check = .ok true ∧
      wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      wire.matchesLast = true := by
  unfold WireRootedOrdinaryProductionRun.terminalAccepted at hcheck
  cases hterminal : wire.terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireRootedOrdinaryProductionRun.check_sound
    (wire : WireRootedOrdinaryProductionRun) (hcheck : wire.check = true) :
    wire.Accepted := by
  simp only [WireRootedOrdinaryProductionRun.check, Bool.and_eq_true] at hcheck
  have hterminal := wire.terminalAccepted_sound hcheck.2
  exact ⟨wire.trace.check_sound hcheck.1.2, hterminal.1,
    hterminal.2.1, hterminal.2.2⟩

theorem WireRootedOrdinaryProductionRun.Accepted.terminal_semantics
    {wire : WireRootedOrdinaryProductionRun} (accepted : wire.Accepted) :
    ∃ decoded : DecodedNativeABoxDecision,
      wire.terminal.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  have hterminal := accepted.terminal
  unfold WireNativeABoxDecisionCertificate.check at hterminal
  cases hdecode : wire.terminal.decode with
  | error message => simp [hdecode] at hterminal
  | ok decoded => exact ⟨decoded, rfl, decoded.semantic_valid⟩

#print axioms WireRootedOrdinaryProductionRun.check_sound
#print axioms WireRootedOrdinaryProductionRun.Accepted.terminal_semantics

end ContextCalculus.Hypertableau
