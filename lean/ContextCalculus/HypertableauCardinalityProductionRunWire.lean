import ContextCalculus.HypertableauCardinalityDoublingTraceWire
import ContextCalculus.HypertableauCardinalityOutcomeWire

/-!
# Complete single-root cardinality production runs

The terminal is checked as a production-global SAT or UNSAT outcome and bound
to the state-bearing iterative-deepening history that preceded it.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireCardinalityProductionRun where
  version : Nat
  start_budget : Nat
  max_width : Nat
  frontiers : List WireCardinalityAddressRefinementDocument
  terminal : WireCardinalityEqCertificate
deriving FromJson, ToJson, Repr

def WireCardinalityProductionRun.trace
    (wire : WireCardinalityProductionRun) : WireCardinalityDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  max_width := wire.max_width
  frontiers := wire.frontiers
}

def WireCardinalityProductionRun.matchesLast
    (wire : WireCardinalityProductionRun) : Bool :=
  match wire.frontiers.getLast? with
  | none => true
  | some frontier =>
      frontier.variable_count == wire.terminal.certificate.variable_count &&
      frontier.frontier.concept_count == wire.terminal.certificate.concept_count &&
      frontier.frontier.role_count == wire.terminal.certificate.role_count &&
      frontier.frontier.definition_count == wire.terminal.definitions.length &&
      frontier.frontier.max_width == wire.max_width &&
      toJson frontier.ontology == toJson wire.terminal.certificate.ontology &&
      toJson frontier.definitions == toJson wire.terminal.definitions

def WireCardinalityProductionRun.terminalAccepted
    (wire : WireCardinalityProductionRun) : Bool :=
  match wire.terminal.checkProductionGlobal with
  | .ok true =>
      decide (wire.terminal.certificate.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      wire.matchesLast
  | _ => false

def WireCardinalityProductionRun.check
    (wire : WireCardinalityProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireCardinalityProductionRun.Accepted
    (wire : WireCardinalityProductionRun) : Prop where
  trace : WireCardinalityDoublingTrace.ValidFrom wire.start_budget
    wire.max_width wire.frontiers
  terminal : wire.terminal.checkProductionGlobal = .ok true
  withinBudget : wire.terminal.certificate.node_count ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  sameProblem : wire.matchesLast = true

theorem WireCardinalityProductionRun.Accepted.terminal_semantics
    {wire : WireCardinalityProductionRun} (accepted : wire.Accepted) :
    ∃ decoded : DecodedCardinalityEqCertificate,
      wire.terminal.decode = .ok decoded ∧
      ∃ outcome : CheckedCardinalityDecisionOutcome
          decoded.base.conceptCount decoded.base.roleCount decoded.base.variableCount
          decoded.base.rootCertificate.base.ontology decoded.definitions,
        outcome.Semantics :=
  wire.terminal.checkProductionGlobal_sound accepted.terminal

theorem WireCardinalityProductionRun.terminalAccepted_sound
    (wire : WireCardinalityProductionRun)
    (hcheck : wire.terminalAccepted = true) :
    wire.terminal.checkProductionGlobal = .ok true ∧
      wire.terminal.certificate.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      wire.matchesLast = true := by
  unfold WireCardinalityProductionRun.terminalAccepted at hcheck
  cases hterminal : wire.terminal.checkProductionGlobal with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireCardinalityProductionRun.check_sound
    (wire : WireCardinalityProductionRun) (hcheck : wire.check = true) :
    wire.Accepted := by
  simp only [WireCardinalityProductionRun.check, Bool.and_eq_true] at hcheck
  have htrace := wire.trace.check_sound hcheck.1.2
  have hterminal := wire.terminalAccepted_sound hcheck.2
  exact ⟨htrace, hterminal.1, hterminal.2.1, hterminal.2.2⟩

#print axioms WireCardinalityProductionRun.check_sound
#print axioms WireCardinalityProductionRun.Accepted.terminal_semantics

end ContextCalculus.Hypertableau
