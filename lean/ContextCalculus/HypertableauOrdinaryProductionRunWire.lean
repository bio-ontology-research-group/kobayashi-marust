import ContextCalculus.HypertableauDoublingTraceWire
import ContextCalculus.HypertableauFiniteProductionTerminalWire
import ContextCalculus.HypertableauRegularProductionTerminalWire
import ContextCalculus.HypertableauEqualityProductionBlockingWire

/-!
# Complete ordinary HT production runs

This wire binds a complete sequence of checked iterative-deepening frontiers
to exactly one checked production SAT terminal. The terminal is reached at the
next scheduled budget, may use fewer nodes than that cap, and must retain the
same finite signature and ontology as the preceding checked frontiers.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireOrdinaryProductionRun where
  version : Nat
  start_budget : Nat
  frontiers : List WireAddressRefinementDocument
  finite : Option WireFiniteProductionTerminal := none
  regular : Option WireRegularProductionTerminal := none
  equality : Option WireEqProductionTerminal := none
deriving FromJson, ToJson, Repr

def WireCertificate.problemMatches
    (left right : WireCertificate) : Bool :=
  left.concept_count == right.concept_count &&
    left.role_count == right.role_count &&
    left.variable_count == right.variable_count &&
    toJson left.ontology == toJson right.ontology

def WireCertificate.eqProblemMatches
    (left : WireCertificate) (right : WireEqCertificate) : Bool :=
  left.concept_count == right.concept_count &&
    left.role_count == right.role_count &&
    left.variable_count == right.variable_count &&
    toJson left.ontology == toJson right.ontology

def WireOrdinaryProductionRun.matchesLast
    (frontiers : List WireAddressRefinementDocument)
    (terminal : WireCertificate) : Bool :=
  match frontiers.getLast? with
  | none => true
  | some frontier => frontier.state.problemMatches terminal

def WireOrdinaryProductionRun.matchesLastEq
    (frontiers : List WireAddressRefinementDocument)
    (terminal : WireEqCertificate) : Bool :=
  match frontiers.getLast? with
  | none => true
  | some frontier => frontier.state.eqProblemMatches terminal

def WireOrdinaryProductionRun.finiteAccepted
    (wire : WireOrdinaryProductionRun)
    (terminal : WireFiniteProductionTerminal) : Bool :=
  match terminal.check with
  | .ok true =>
      decide (terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      WireOrdinaryProductionRun.matchesLast wire.frontiers terminal.table.base
  | _ => false

def WireOrdinaryProductionRun.regularAccepted
    (wire : WireOrdinaryProductionRun)
    (terminal : WireRegularProductionTerminal) : Bool :=
  match terminal.check with
  | .ok true =>
      decide (terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      WireOrdinaryProductionRun.matchesLast wire.frontiers terminal.table.base
  | _ => false

def WireOrdinaryProductionRun.equalityAccepted
    (wire : WireOrdinaryProductionRun)
    (terminal : WireEqProductionTerminal) : Bool :=
  match terminal.check with
  | .ok true =>
      decide (terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length)) &&
      WireOrdinaryProductionRun.matchesLastEq wire.frontiers terminal.table.base
  | _ => false

def WireOrdinaryProductionRun.terminalAccepted
    (wire : WireOrdinaryProductionRun) : Bool :=
  match wire.finite, wire.regular, wire.equality with
  | some terminal, none, none => wire.finiteAccepted terminal
  | none, some terminal, none => wire.regularAccepted terminal
  | none, none, some terminal => wire.equalityAccepted terminal
  | _, _, _ => false

def WireOrdinaryProductionRun.trace
    (wire : WireOrdinaryProductionRun) : WireAddressDoublingTrace := {
  version := 1
  start_budget := wire.start_budget
  frontiers := wire.frontiers
}

def WireOrdinaryProductionRun.check
    (wire : WireOrdinaryProductionRun) : Bool :=
  wire.version == 1 && wire.trace.check && wire.terminalAccepted

inductive WireOrdinaryProductionRun.AcceptedTerminal
    (wire : WireOrdinaryProductionRun) : Prop where
  | finite (terminal : WireFiniteProductionTerminal)
      (shape : wire.finite = some terminal ∧ wire.regular = none ∧
        wire.equality = none)
      (checked : terminal.check = .ok true)
      (withinBudget : terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length))
      (sameProblem : WireOrdinaryProductionRun.matchesLast wire.frontiers
        terminal.table.base = true) :
      WireOrdinaryProductionRun.AcceptedTerminal wire
  | regular (terminal : WireRegularProductionTerminal)
      (shape : wire.finite = none ∧ wire.regular = some terminal ∧
        wire.equality = none)
      (checked : terminal.check = .ok true)
      (withinBudget : terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length))
      (sameProblem : WireOrdinaryProductionRun.matchesLast wire.frontiers
        terminal.table.base = true) :
      WireOrdinaryProductionRun.AcceptedTerminal wire
  | equality (terminal : WireEqProductionTerminal)
      (shape : wire.finite = none ∧ wire.regular = none ∧
        wire.equality = some terminal)
      (checked : terminal.check = .ok true)
      (withinBudget : terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length))
      (sameProblem : WireOrdinaryProductionRun.matchesLastEq wire.frontiers
        terminal.table.base = true) :
      WireOrdinaryProductionRun.AcceptedTerminal wire

theorem WireOrdinaryProductionRun.finiteAccepted_sound
    (wire : WireOrdinaryProductionRun)
    (terminal : WireFiniteProductionTerminal)
    (hcheck : wire.finiteAccepted terminal = true) :
    terminal.check = .ok true ∧
      terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      WireOrdinaryProductionRun.matchesLast wire.frontiers
        terminal.table.base = true := by
  unfold WireOrdinaryProductionRun.finiteAccepted at hcheck
  cases hterminal : terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireOrdinaryProductionRun.regularAccepted_sound
    (wire : WireOrdinaryProductionRun)
    (terminal : WireRegularProductionTerminal)
    (hcheck : wire.regularAccepted terminal = true) :
    terminal.check = .ok true ∧
      terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      WireOrdinaryProductionRun.matchesLast wire.frontiers
        terminal.table.base = true := by
  unfold WireOrdinaryProductionRun.regularAccepted at hcheck
  cases hterminal : terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireOrdinaryProductionRun.equalityAccepted_sound
    (wire : WireOrdinaryProductionRun)
    (terminal : WireEqProductionTerminal)
    (hcheck : wire.equalityAccepted terminal = true) :
    terminal.check = .ok true ∧
      terminal.table.base.node_count ≤
        8 * 2 ^ (wire.start_budget + wire.frontiers.length) ∧
      WireOrdinaryProductionRun.matchesLastEq wire.frontiers
        terminal.table.base = true := by
  unfold WireOrdinaryProductionRun.equalityAccepted at hcheck
  cases hterminal : terminal.check with
  | error message => simp [hterminal] at hcheck
  | ok accepted =>
      cases accepted <;> simp [hterminal, Bool.and_eq_true,
        decide_eq_true_eq] at hcheck ⊢
      exact hcheck

theorem WireOrdinaryProductionRun.terminalAccepted_sound
    (wire : WireOrdinaryProductionRun)
    (hcheck : wire.terminalAccepted = true) : wire.AcceptedTerminal := by
  unfold WireOrdinaryProductionRun.terminalAccepted at hcheck
  cases hfinite : wire.finite with
  | none =>
      cases hregular : wire.regular with
      | none =>
          cases hequality : wire.equality with
          | none => simp [hfinite, hregular, hequality] at hcheck
          | some terminal =>
              have accepted := wire.equalityAccepted_sound terminal (by
                simpa [hfinite, hregular, hequality] using hcheck)
              exact .equality terminal ⟨hfinite, hregular, hequality⟩
                accepted.1 accepted.2.1 accepted.2.2
      | some terminal =>
          cases hequality : wire.equality with
          | none =>
              have accepted := wire.regularAccepted_sound terminal (by
                simpa [hfinite, hregular, hequality] using hcheck)
              exact .regular terminal ⟨hfinite, hregular, hequality⟩
                accepted.1 accepted.2.1 accepted.2.2
          | some equality => simp [hfinite, hregular, hequality] at hcheck
  | some terminal =>
      cases hregular : wire.regular with
      | none =>
          cases hequality : wire.equality with
          | none =>
              have accepted := wire.finiteAccepted_sound terminal (by
                simpa [hfinite, hregular, hequality] using hcheck)
              exact .finite terminal ⟨hfinite, hregular, hequality⟩
                accepted.1 accepted.2.1 accepted.2.2
          | some equality => simp [hfinite, hregular, hequality] at hcheck
      | some regular => simp [hfinite, hregular] at hcheck

theorem WireOrdinaryProductionRun.check_sound
    (wire : WireOrdinaryProductionRun) (hcheck : wire.check = true) :
    WireAddressDoublingTrace.ValidFrom wire.start_budget wire.frontiers ∧
      wire.AcceptedTerminal := by
  simp only [WireOrdinaryProductionRun.check, Bool.and_eq_true] at hcheck
  exact ⟨wire.trace.check_sound hcheck.1.2,
    wire.terminalAccepted_sound hcheck.2⟩

#print axioms WireOrdinaryProductionRun.check_sound

end ContextCalculus.Hypertableau
