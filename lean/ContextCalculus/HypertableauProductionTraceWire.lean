import ContextCalculus.HypertableauProductionBlockingWire

/-!
# Equality-free production execution history

Each entry is a checked blocker document emitted after one complete Cartesian
assignment product has been rejected. The history additionally checks that the
first rerun starts with no forbidden pair and that every later rerun forbids
exactly the preceding set union the complete option-pair set learned there.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireProductionExecutionTrace where
  version : Nat
  rounds : List WireProductionBlockingTable
deriving FromJson, ToJson, Repr

private def natPair (pair : WireNodePair) : Nat × Nat :=
  (pair.source, pair.target)

def WireProductionBlockingTable.forbiddenNat
    (wire : WireProductionBlockingTable) : Finset (Nat × Nat) :=
  (wire.forbidden.map natPair).toFinset

def WireProductionBlockingTable.optionPairsNat
    (wire : WireProductionBlockingTable) : Finset (Nat × Nat) :=
  (wire.options.flatMap fun option =>
    option.blockers.map fun blocker => (option.source, blocker)).toFinset

def WireProductionBlockingTable.accepted
    (wire : WireProductionBlockingTable) : Bool :=
  match wire.check with
  | .ok true => true
  | _ => false

def WireProductionBlockingTable.sameProblem
    (left right : WireProductionBlockingTable) : Bool :=
  left.base.node_count == right.base.node_count &&
    left.base.concept_count == right.base.concept_count &&
    left.base.role_count == right.base.role_count &&
    left.base.variable_count == right.base.variable_count &&
    toJson left.base.ontology == toJson right.base.ontology

def WireProductionBlockingTable.nextForbiddenExact
    (current next : WireProductionBlockingTable) : Bool :=
  next.forbiddenNat == current.forbiddenNat ∪ current.optionPairsNat

def WireProductionExecutionTrace.transitionsValid :
    List WireProductionBlockingTable → Bool
  | [] | [_] => true
  | current :: next :: rest =>
      current.sameProblem next && current.nextForbiddenExact next &&
        transitionsValid (next :: rest)

def WireProductionExecutionTrace.check
    (wire : WireProductionExecutionTrace) : Bool :=
  wire.version == 1 &&
    match wire.rounds with
    | [] => false
    | first :: _ =>
        wire.rounds.all WireProductionBlockingTable.accepted &&
          decide (first.forbiddenNat = ∅) &&
          WireProductionExecutionTrace.transitionsValid wire.rounds

inductive WireProductionExecutionTrace.ValidFrom :
    Finset (Nat × Nat) → List WireProductionBlockingTable → Prop where
  | last
      (expected : Finset (Nat × Nat))
      (round : WireProductionBlockingTable)
      (accepted : round.check = .ok true)
      (forbidden : round.forbiddenNat = expected) :
      WireProductionExecutionTrace.ValidFrom expected [round]
  | step
      (expected : Finset (Nat × Nat))
      (current next : WireProductionBlockingTable)
      (rest : List WireProductionBlockingTable)
      (accepted : current.check = .ok true)
      (forbidden : current.forbiddenNat = expected)
      (sameProblem : current.sameProblem next = true)
      (nextForbidden : next.forbiddenNat =
        current.forbiddenNat ∪ current.optionPairsNat)
      (tail : WireProductionExecutionTrace.ValidFrom next.forbiddenNat
        (next :: rest)) :
      WireProductionExecutionTrace.ValidFrom expected
        (current :: next :: rest)

theorem WireProductionBlockingTable.accepted_eq_true_iff
    (wire : WireProductionBlockingTable) :
    wire.accepted = true ↔ wire.check = .ok true := by
  unfold WireProductionBlockingTable.accepted
  cases hcheck : wire.check <;> simp
  rename_i value
  cases value <;> simp

theorem WireProductionExecutionTrace.transitionsValid_head
    {current next : WireProductionBlockingTable}
    {rest : List WireProductionBlockingTable}
    (hvalid : WireProductionExecutionTrace.transitionsValid
      (current :: next :: rest) = true) :
    current.sameProblem next = true ∧
      current.nextForbiddenExact next = true ∧
      WireProductionExecutionTrace.transitionsValid (next :: rest) = true := by
  simp only [WireProductionExecutionTrace.transitionsValid,
    Bool.and_eq_true] at hvalid
  exact ⟨hvalid.1.1, hvalid.1.2, hvalid.2⟩

theorem WireProductionExecutionTrace.validFrom_of_checks
    (rounds : List WireProductionBlockingTable)
    (expected : Finset (Nat × Nat))
    (hnonempty : rounds ≠ [])
    (hall : rounds.all WireProductionBlockingTable.accepted = true)
    (htransitions : WireProductionExecutionTrace.transitionsValid rounds = true)
    (hfirst : ∃ first rest, rounds = first :: rest ∧
      first.forbiddenNat = expected) :
    WireProductionExecutionTrace.ValidFrom expected rounds := by
  induction rounds generalizing expected with
  | nil => exact False.elim (hnonempty rfl)
  | cons current rest ih =>
      rcases hfirst with ⟨first, suffix, hrounds, hforbidden⟩
      cases hrounds
      cases rest with
      | nil =>
          apply WireProductionExecutionTrace.ValidFrom.last
          · exact current.accepted_eq_true_iff.mp (by simpa using hall)
          · exact hforbidden
      | cons next tail =>
          have htransition :=
            WireProductionExecutionTrace.transitionsValid_head htransitions
          apply WireProductionExecutionTrace.ValidFrom.step
          · exact current.accepted_eq_true_iff.mp
              ((List.all_eq_true.mp hall) current (by simp))
          · exact hforbidden
          · exact htransition.1
          · exact beq_iff_eq.mp htransition.2.1
          · have hallTail :
                (next :: tail).all WireProductionBlockingTable.accepted = true := by
              simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
              exact hall.2
            exact ih next.forbiddenNat (by simp) hallTail htransition.2.2
              ⟨next, tail, rfl, rfl⟩

theorem WireProductionExecutionTrace.check_validFrom_empty
    (wire : WireProductionExecutionTrace)
    (hcheck : wire.check = true) :
    WireProductionExecutionTrace.ValidFrom ∅ wire.rounds := by
  unfold WireProductionExecutionTrace.check at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i first rest heq
    simp only [Bool.and_eq_true] at hcheck
    have hnonempty : wire.rounds ≠ [] := by rw [heq]; simp
    exact WireProductionExecutionTrace.validFrom_of_checks wire.rounds ∅
      hnonempty hcheck.2.1.1 hcheck.2.2
      ⟨first, rest, heq, of_decide_eq_true hcheck.2.1.2⟩

theorem WireProductionExecutionTrace.check_first_transition
    (wire : WireProductionExecutionTrace)
    {current next : WireProductionBlockingTable}
    {rest : List WireProductionBlockingTable}
    (hrounds : wire.rounds = current :: next :: rest)
    (hcheck : wire.check = true) :
    current.sameProblem next = true ∧
      next.forbiddenNat = current.forbiddenNat ∪ current.optionPairsNat := by
  unfold WireProductionExecutionTrace.check at hcheck
  rw [hrounds] at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have htransition :=
    WireProductionExecutionTrace.transitionsValid_head hcheck.2.2
  exact ⟨htransition.1, beq_iff_eq.mp htransition.2.1⟩

#print axioms WireProductionExecutionTrace.validFrom_of_checks
#print axioms WireProductionExecutionTrace.check_validFrom_empty
#print axioms WireProductionExecutionTrace.check_first_transition

end ContextCalculus.Hypertableau
