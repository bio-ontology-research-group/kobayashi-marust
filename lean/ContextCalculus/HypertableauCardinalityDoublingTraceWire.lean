import ContextCalculus.HypertableauCardinalityFrontierStateWire

/-!
# Cardinality frontier-doubling execution histories

These wires check complete iterative-deepening histories for the single-root
and native-ABox multi-root cardinality searches. Each successive frontier is
checked at the next doubling budget, and all dimensions that determine the
finite address space remain fixed throughout the run.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireCardinalityDoublingTrace where
  version : Nat
  start_budget : Nat
  max_width : Nat
  frontiers : List WireCardinalityAddressRefinementDocument
deriving FromJson, ToJson, Repr

def WireCardinalityDoublingTrace.scheduledFrom :
    Nat → Nat → List WireCardinalityAddressRefinementDocument → Bool
  | _, _, [] => true
  | budget, maxWidth, current :: rest =>
      current.checkScheduled budget maxWidth &&
        scheduledFrom (budget + 1) maxWidth rest

def WireCardinalityDoublingTrace.sameProblemThroughout :
    List WireCardinalityAddressRefinementDocument → Bool
  | [] | [_] => true
  | current :: next :: rest =>
      current.sameProblem next && sameProblemThroughout (next :: rest)

def WireCardinalityDoublingTrace.check
    (wire : WireCardinalityDoublingTrace) : Bool :=
  wire.version == 1 &&
    WireCardinalityDoublingTrace.scheduledFrom wire.start_budget
      wire.max_width wire.frontiers &&
    WireCardinalityDoublingTrace.sameProblemThroughout wire.frontiers

inductive WireCardinalityDoublingTrace.ValidFrom :
    Nat → Nat → List WireCardinalityAddressRefinementDocument → Prop where
  | nil (budget maxWidth : Nat) :
      WireCardinalityDoublingTrace.ValidFrom budget maxWidth []
  | last (budget maxWidth : Nat) (current : WireCardinalityAddressRefinementDocument)
      (scheduled : current.checkScheduled budget maxWidth = true) :
      WireCardinalityDoublingTrace.ValidFrom budget maxWidth [current]
  | step (budget maxWidth : Nat)
      (current next : WireCardinalityAddressRefinementDocument)
      (rest : List WireCardinalityAddressRefinementDocument)
      (scheduled : current.checkScheduled budget maxWidth = true)
      (sameProblem : current.sameProblem next = true)
      (tail : WireCardinalityDoublingTrace.ValidFrom (budget + 1)
        maxWidth (next :: rest)) :
      WireCardinalityDoublingTrace.ValidFrom budget maxWidth
        (current :: next :: rest)

theorem WireCardinalityDoublingTrace.scheduledFrom_tail
    {budget maxWidth : Nat}
    {current next : WireCardinalityAddressRefinementDocument}
    {rest : List WireCardinalityAddressRefinementDocument}
    (hcheck : WireCardinalityDoublingTrace.scheduledFrom budget maxWidth
      (current :: next :: rest) = true) :
    current.checkScheduled budget maxWidth = true ∧
      WireCardinalityDoublingTrace.scheduledFrom (budget + 1) maxWidth
        (next :: rest) = true := by
  simpa [WireCardinalityDoublingTrace.scheduledFrom] using hcheck

theorem WireCardinalityDoublingTrace.sameProblemThroughout_tail
    {current next : WireCardinalityAddressRefinementDocument}
    {rest : List WireCardinalityAddressRefinementDocument}
    (hcheck : WireCardinalityDoublingTrace.sameProblemThroughout
      (current :: next :: rest) = true) :
    current.sameProblem next = true ∧
      WireCardinalityDoublingTrace.sameProblemThroughout
        (next :: rest) = true := by
  simpa [WireCardinalityDoublingTrace.sameProblemThroughout] using hcheck

theorem WireCardinalityDoublingTrace.validFrom_of_checks
    (budget maxWidth : Nat) (frontiers : List WireCardinalityAddressRefinementDocument)
    (hscheduled : WireCardinalityDoublingTrace.scheduledFrom budget maxWidth
      frontiers = true)
    (hsame : WireCardinalityDoublingTrace.sameProblemThroughout frontiers = true) :
    WireCardinalityDoublingTrace.ValidFrom budget maxWidth frontiers := by
  induction frontiers generalizing budget with
  | nil => exact .nil budget maxWidth
  | cons current rest ih =>
      cases rest with
      | nil =>
          exact .last budget maxWidth current (by
            simpa [WireCardinalityDoublingTrace.scheduledFrom] using hscheduled)
      | cons next tail =>
          have scheduled := WireCardinalityDoublingTrace.scheduledFrom_tail hscheduled
          have same := WireCardinalityDoublingTrace.sameProblemThroughout_tail hsame
          exact .step budget maxWidth current next tail scheduled.1 same.1
            (ih (budget + 1) scheduled.2 same.2)

theorem WireCardinalityDoublingTrace.check_sound
    (wire : WireCardinalityDoublingTrace) (hcheck : wire.check = true) :
    WireCardinalityDoublingTrace.ValidFrom wire.start_budget wire.max_width
      wire.frontiers := by
  simp only [WireCardinalityDoublingTrace.check, Bool.and_eq_true] at hcheck
  exact WireCardinalityDoublingTrace.validFrom_of_checks wire.start_budget
    wire.max_width wire.frontiers hcheck.1.2 hcheck.2

structure WireRootedCardinalityDoublingTrace where
  version : Nat
  start_budget : Nat
  root_count : Nat
  max_width : Nat
  frontiers : List WireRootedCardinalityAddressRefinementDocument
deriving FromJson, ToJson, Repr

def WireRootedCardinalityDoublingTrace.scheduledFrom :
    Nat → Nat → Nat → List WireRootedCardinalityAddressRefinementDocument → Bool
  | _, _, _, [] => true
  | budget, rootCount, maxWidth, current :: rest =>
      current.checkScheduled budget rootCount maxWidth &&
        scheduledFrom (budget + 1) rootCount maxWidth rest

def WireRootedCardinalityDoublingTrace.sameProblemThroughout :
    List WireRootedCardinalityAddressRefinementDocument → Bool
  | [] | [_] => true
  | current :: next :: rest =>
      current.sameProblem next && sameProblemThroughout (next :: rest)

def WireRootedCardinalityDoublingTrace.check
    (wire : WireRootedCardinalityDoublingTrace) : Bool :=
  wire.version == 1 &&
    WireRootedCardinalityDoublingTrace.scheduledFrom wire.start_budget
      wire.root_count wire.max_width wire.frontiers &&
    WireRootedCardinalityDoublingTrace.sameProblemThroughout wire.frontiers

inductive WireRootedCardinalityDoublingTrace.ValidFrom :
    Nat → Nat → Nat → List WireRootedCardinalityAddressRefinementDocument → Prop where
  | nil (budget rootCount maxWidth : Nat) :
      WireRootedCardinalityDoublingTrace.ValidFrom budget rootCount maxWidth []
  | last (budget rootCount maxWidth : Nat)
      (current : WireRootedCardinalityAddressRefinementDocument)
      (scheduled : current.checkScheduled budget rootCount maxWidth = true) :
      WireRootedCardinalityDoublingTrace.ValidFrom budget rootCount maxWidth [current]
  | step (budget rootCount maxWidth : Nat)
      (current next : WireRootedCardinalityAddressRefinementDocument)
      (rest : List WireRootedCardinalityAddressRefinementDocument)
      (scheduled : current.checkScheduled budget rootCount maxWidth = true)
      (sameProblem : current.sameProblem next = true)
      (tail : WireRootedCardinalityDoublingTrace.ValidFrom (budget + 1)
        rootCount maxWidth (next :: rest)) :
      WireRootedCardinalityDoublingTrace.ValidFrom budget rootCount maxWidth
        (current :: next :: rest)

theorem WireRootedCardinalityDoublingTrace.scheduledFrom_tail
    {budget rootCount maxWidth : Nat}
    {current next : WireRootedCardinalityAddressRefinementDocument}
    {rest : List WireRootedCardinalityAddressRefinementDocument}
    (hcheck : WireRootedCardinalityDoublingTrace.scheduledFrom budget rootCount
      maxWidth (current :: next :: rest) = true) :
    current.checkScheduled budget rootCount maxWidth = true ∧
      WireRootedCardinalityDoublingTrace.scheduledFrom (budget + 1)
        rootCount maxWidth (next :: rest) = true := by
  simpa [WireRootedCardinalityDoublingTrace.scheduledFrom] using hcheck

theorem WireRootedCardinalityDoublingTrace.sameProblemThroughout_tail
    {current next : WireRootedCardinalityAddressRefinementDocument}
    {rest : List WireRootedCardinalityAddressRefinementDocument}
    (hcheck : WireRootedCardinalityDoublingTrace.sameProblemThroughout
      (current :: next :: rest) = true) :
    current.sameProblem next = true ∧
      WireRootedCardinalityDoublingTrace.sameProblemThroughout
        (next :: rest) = true := by
  simpa [WireRootedCardinalityDoublingTrace.sameProblemThroughout] using hcheck

theorem WireRootedCardinalityDoublingTrace.validFrom_of_checks
    (budget rootCount maxWidth : Nat)
    (frontiers : List WireRootedCardinalityAddressRefinementDocument)
    (hscheduled : WireRootedCardinalityDoublingTrace.scheduledFrom budget
      rootCount maxWidth frontiers = true)
    (hsame : WireRootedCardinalityDoublingTrace.sameProblemThroughout frontiers = true) :
    WireRootedCardinalityDoublingTrace.ValidFrom budget rootCount maxWidth
      frontiers := by
  induction frontiers generalizing budget with
  | nil => exact .nil budget rootCount maxWidth
  | cons current rest ih =>
      cases rest with
      | nil =>
          exact .last budget rootCount maxWidth current (by
            simpa [WireRootedCardinalityDoublingTrace.scheduledFrom] using hscheduled)
      | cons next tail =>
          have scheduled :=
            WireRootedCardinalityDoublingTrace.scheduledFrom_tail hscheduled
          have same :=
            WireRootedCardinalityDoublingTrace.sameProblemThroughout_tail hsame
          exact .step budget rootCount maxWidth current next tail scheduled.1
            same.1 (ih (budget + 1) scheduled.2 same.2)

theorem WireRootedCardinalityDoublingTrace.check_sound
    (wire : WireRootedCardinalityDoublingTrace) (hcheck : wire.check = true) :
    WireRootedCardinalityDoublingTrace.ValidFrom wire.start_budget
      wire.root_count wire.max_width wire.frontiers := by
  simp only [WireRootedCardinalityDoublingTrace.check, Bool.and_eq_true] at hcheck
  exact WireRootedCardinalityDoublingTrace.validFrom_of_checks wire.start_budget
    wire.root_count wire.max_width wire.frontiers hcheck.1.2 hcheck.2

#print axioms WireCardinalityDoublingTrace.check_sound
#print axioms WireRootedCardinalityDoublingTrace.check_sound

end ContextCalculus.Hypertableau
