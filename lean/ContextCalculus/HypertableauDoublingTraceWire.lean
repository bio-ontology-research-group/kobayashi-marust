import ContextCalculus.HypertableauAddressRefinementWire

/-!
# Equality-free and equality-aware frontier-doubling execution history

This wire checks the sequence of bounded frontiers traversed by KM before a
terminal result. Every frontier carries its exact finite state and rooted
address refinement. The first document is checked at `startBudget`; each later
document is checked at the successor budget and must retain the same ontology
and finite vocabulary.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireAddressDoublingTrace where
  version : Nat
  start_budget : Nat
  frontiers : List WireAddressRefinementDocument
deriving FromJson, ToJson, Repr

def WireAddressRefinementDocument.sameProblem
    (left right : WireAddressRefinementDocument) : Bool :=
  left.state.concept_count == right.state.concept_count &&
    left.state.role_count == right.state.role_count &&
    left.state.variable_count == right.state.variable_count &&
    toJson left.state.ontology == toJson right.state.ontology

def WireAddressRefinementDocument.acceptedScheduled
    (document : WireAddressRefinementDocument) (budget : Nat) : Bool :=
  match document.check with
  | .ok true => document.frontier.checkScheduled budget
  | _ => false

def WireAddressDoublingTrace.scheduledFrom :
    Nat → List WireAddressRefinementDocument → Bool
  | _, [] => true
  | budget, document :: rest =>
      document.acceptedScheduled budget && scheduledFrom (budget + 1) rest

def WireAddressDoublingTrace.sameProblemThroughout :
    List WireAddressRefinementDocument → Bool
  | [] | [_] => true
  | current :: next :: rest =>
      current.sameProblem next && sameProblemThroughout (next :: rest)

def WireAddressDoublingTrace.check
    (wire : WireAddressDoublingTrace) : Bool :=
  wire.version == 1 &&
    WireAddressDoublingTrace.scheduledFrom wire.start_budget wire.frontiers &&
    WireAddressDoublingTrace.sameProblemThroughout wire.frontiers

inductive WireAddressDoublingTrace.ValidFrom :
    Nat → List WireAddressRefinementDocument → Prop where
  | nil (budget : Nat) : WireAddressDoublingTrace.ValidFrom budget []
  | last
      (budget : Nat)
      (document : WireAddressRefinementDocument)
      (accepted : document.check = .ok true)
      (scheduled : document.frontier.checkScheduled budget = true) :
      WireAddressDoublingTrace.ValidFrom budget [document]
  | step
      (budget : Nat)
      (current next : WireAddressRefinementDocument)
      (rest : List WireAddressRefinementDocument)
      (accepted : current.check = .ok true)
      (scheduled : current.frontier.checkScheduled budget = true)
      (sameProblem : current.sameProblem next = true)
      (tail : WireAddressDoublingTrace.ValidFrom (budget + 1)
        (next :: rest)) :
      WireAddressDoublingTrace.ValidFrom budget (current :: next :: rest)

theorem WireAddressRefinementDocument.acceptedScheduled_eq_true_iff
    (document : WireAddressRefinementDocument) (budget : Nat) :
    document.acceptedScheduled budget = true ↔
      document.check = .ok true ∧
      document.frontier.checkScheduled budget = true := by
  unfold WireAddressRefinementDocument.acceptedScheduled
  cases hcheck : document.check <;> simp
  rename_i value
  cases value <;> simp

theorem WireAddressDoublingTrace.scheduledFrom_tail
    {budget : Nat} {current next : WireAddressRefinementDocument}
    {rest : List WireAddressRefinementDocument}
    (hcheck : WireAddressDoublingTrace.scheduledFrom budget
      (current :: next :: rest) = true) :
    current.acceptedScheduled budget = true ∧
      WireAddressDoublingTrace.scheduledFrom (budget + 1)
        (next :: rest) = true := by
  simpa [WireAddressDoublingTrace.scheduledFrom] using hcheck

theorem WireAddressDoublingTrace.sameProblemThroughout_tail
    {current next : WireAddressRefinementDocument}
    {rest : List WireAddressRefinementDocument}
    (hcheck : WireAddressDoublingTrace.sameProblemThroughout
      (current :: next :: rest) = true) :
    current.sameProblem next = true ∧
      WireAddressDoublingTrace.sameProblemThroughout (next :: rest) = true := by
  simpa [WireAddressDoublingTrace.sameProblemThroughout] using hcheck

theorem WireAddressDoublingTrace.validFrom_of_checks
    (budget : Nat) (frontiers : List WireAddressRefinementDocument)
    (hscheduled : WireAddressDoublingTrace.scheduledFrom budget frontiers = true)
    (hsame : WireAddressDoublingTrace.sameProblemThroughout frontiers = true) :
    WireAddressDoublingTrace.ValidFrom budget frontiers := by
  induction frontiers generalizing budget with
  | nil => exact .nil budget
  | cons current rest ih =>
      cases rest with
      | nil =>
          have accepted :=
            (current.acceptedScheduled_eq_true_iff budget).mp (by
              simpa [WireAddressDoublingTrace.scheduledFrom] using hscheduled)
          exact .last budget current accepted.1 accepted.2
      | cons next tail =>
          have scheduled :=
            WireAddressDoublingTrace.scheduledFrom_tail hscheduled
          have same :=
            WireAddressDoublingTrace.sameProblemThroughout_tail hsame
          have accepted :=
            (current.acceptedScheduled_eq_true_iff budget).mp scheduled.1
          exact .step budget current next tail accepted.1 accepted.2 same.1
            (ih (budget + 1) scheduled.2 same.2)

theorem WireAddressDoublingTrace.check_sound
    (wire : WireAddressDoublingTrace)
    (hcheck : wire.check = true) :
    WireAddressDoublingTrace.ValidFrom wire.start_budget wire.frontiers := by
  simp only [WireAddressDoublingTrace.check, Bool.and_eq_true] at hcheck
  exact WireAddressDoublingTrace.validFrom_of_checks wire.start_budget
    wire.frontiers hcheck.1.2 hcheck.2

#print axioms WireAddressDoublingTrace.check_sound

end ContextCalculus.Hypertableau
