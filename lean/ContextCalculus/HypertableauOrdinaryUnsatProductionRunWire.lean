import ContextCalculus.HypertableauDoublingTraceWire
import ContextCalculus.HypertableauEqualityWire

/-!
# Complete ordinary HT UNSAT production runs

This wire binds an ordinary or equality-aware UNSAT terminal to every checked
iterative-deepening frontier traversed by the production run that produced its
exact closing tree.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireOrdinaryUnsatProductionTerminal where
  | ordinary (certificate : WireCertificate)
  | equality (certificate : WireEqCertificate)
deriving FromJson, ToJson, Repr

structure WireOrdinaryUnsatProductionRun where
  version : Nat
  start_budget : Nat
  frontiers : List WireAddressRefinementDocument
  terminal : WireOrdinaryUnsatProductionTerminal
deriving FromJson, ToJson, Repr

def WireOrdinaryUnsatProductionRun.trace
    (wire : WireOrdinaryUnsatProductionRun) : WireAddressDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  frontiers := wire.frontiers
}

def WireOrdinaryUnsatProductionTerminal.nodeCount :
    WireOrdinaryUnsatProductionTerminal → Nat
  | .ordinary certificate => certificate.node_count
  | .equality certificate => certificate.node_count

def WireOrdinaryUnsatProductionTerminal.matchesLast
    (terminal : WireOrdinaryUnsatProductionTerminal)
    (frontiers : List WireAddressRefinementDocument) : Bool :=
  match frontiers.getLast? with
  | none => true
  | some frontier =>
      match terminal with
      | .ordinary certificate =>
          frontier.state.concept_count == certificate.concept_count &&
          frontier.state.role_count == certificate.role_count &&
          frontier.state.variable_count == certificate.variable_count &&
          toJson frontier.state.ontology == toJson certificate.ontology
      | .equality certificate =>
          frontier.state.concept_count == certificate.concept_count &&
          frontier.state.role_count == certificate.role_count &&
          frontier.state.variable_count == certificate.variable_count &&
          toJson frontier.state.ontology == toJson certificate.ontology

def WireOrdinaryUnsatProductionTerminal.isUnsat :
    WireOrdinaryUnsatProductionTerminal → Bool
  | .ordinary certificate =>
    match certificate.decode with
    | .error _ => false
    | .ok decoded =>
      match decoded with
      | .unsat _ _ => true
      | _ => false
  | .equality certificate =>
    match certificate.decode with
    | .error _ => false
    | .ok decoded =>
      match decoded.evidence with
      | .unsat _ _ => true
      | _ => false

def WireOrdinaryUnsatProductionTerminal.check :
    WireOrdinaryUnsatProductionTerminal → Except String Bool
  | .ordinary certificate => certificate.check
  | .equality certificate => certificate.check

def WireOrdinaryUnsatProductionRun.terminalAccepted
    (wire : WireOrdinaryUnsatProductionRun) : Bool :=
  match wire.terminal.check with
  | .ok true =>
      wire.terminal.isUnsat &&
      decide (wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      wire.terminal.matchesLast wire.frontiers
  | _ => false

def WireOrdinaryUnsatProductionRun.check
    (wire : WireOrdinaryUnsatProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

structure WireOrdinaryUnsatProductionRun.Accepted
    (wire : WireOrdinaryUnsatProductionRun) : Prop where
  trace : WireAddressDoublingTrace.ValidFrom wire.start_budget wire.frontiers
  unsat : wire.terminal.isUnsat = true
  terminal : wire.terminal.check = .ok true
  withinBudget : wire.terminal.nodeCount ≤
    8 * 2 ^ (wire.start_budget + wire.frontiers.length)
  sameProblem : wire.terminal.matchesLast wire.frontiers = true

theorem WireOrdinaryUnsatProductionRun.terminalAccepted_sound
    (wire : WireOrdinaryUnsatProductionRun)
    (hcheck : wire.terminalAccepted = true) :
    wire.terminal.isUnsat = true ∧ wire.terminal.check = .ok true ∧
      wire.terminal.nodeCount ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      wire.terminal.matchesLast wire.frontiers = true := by
  unfold WireOrdinaryUnsatProductionRun.terminalAccepted at hcheck
  cases hterminal : wire.terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted with
      | false => simp [hterminal] at hcheck
      | true =>
          have parts :
              (wire.terminal.isUnsat = true ∧
                wire.terminal.nodeCount ≤
                  8 * 2 ^ (wire.start_budget + wire.frontiers.length)) ∧
                wire.terminal.matchesLast wire.frontiers = true := by
            simpa [hterminal, Bool.and_eq_true, decide_eq_true_eq] using hcheck
          exact ⟨parts.1.1, rfl, parts.1.2, parts.2⟩

def WireOrdinaryUnsatProductionTerminal.SemanticallyValid :
    WireOrdinaryUnsatProductionTerminal → Prop
  | .ordinary certificate =>
      ∃ decoded, certificate.decode = .ok decoded ∧ decoded.SemanticallyValid
  | .equality certificate =>
      ∃ decoded, certificate.decode = .ok decoded ∧ decoded.SemanticallyValid

theorem WireOrdinaryUnsatProductionTerminal.semantic_valid
    (terminal : WireOrdinaryUnsatProductionTerminal)
    (hcheck : terminal.check = .ok true) : terminal.SemanticallyValid := by
  cases terminal with
  | ordinary certificate =>
      simp only [WireOrdinaryUnsatProductionTerminal.SemanticallyValid]
      change certificate.check = .ok true at hcheck
      exact WireCertificate.check_sound certificate hcheck
  | equality certificate =>
      simp only [WireOrdinaryUnsatProductionTerminal.SemanticallyValid]
      change certificate.check = .ok true at hcheck
      unfold WireEqCertificate.check at hcheck
      generalize hdecode : certificate.decode = result at hcheck ⊢
      cases result with
      | error message => cases hcheck
      | ok decoded =>
          have hok : Except.ok decoded.check =
              (Except.ok true : Except String Bool) := by simpa using hcheck
          injection hok with hvalid
          exact ⟨decoded, rfl, decoded.check_sound hvalid⟩

theorem WireOrdinaryUnsatProductionRun.check_sound
    (wire : WireOrdinaryUnsatProductionRun) (hcheck : wire.check = true) :
    wire.Accepted := by
  simp only [WireOrdinaryUnsatProductionRun.check, Bool.and_eq_true] at hcheck
  have hterminal := wire.terminalAccepted_sound hcheck.2
  exact ⟨wire.trace.check_sound hcheck.1.2, hterminal.1,
    hterminal.2.1, hterminal.2.2.1, hterminal.2.2.2⟩

theorem WireOrdinaryUnsatProductionRun.Accepted.terminal_semantics
    {wire : WireOrdinaryUnsatProductionRun} (accepted : wire.Accepted) :
    wire.terminal.SemanticallyValid :=
  wire.terminal.semantic_valid accepted.terminal

#print axioms WireOrdinaryUnsatProductionRun.check_sound
#print axioms WireOrdinaryUnsatProductionRun.Accepted.terminal_semantics

end ContextCalculus.Hypertableau
