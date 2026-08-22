import ContextCalculus.HypertableauEqualityProductionBlockingWire

/-!
# Equality-aware production execution history

Each entry is the already checked blocker document emitted after one complete
Cartesian assignment product has been rejected.  This wire additionally checks
the transition between entries: the next rerun must forbid exactly the prior
forbidden set union the complete option-pair set learned at exhaustion.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireEqProductionExecutionTrace where
  version : Nat
  rounds : List WireEqProductionBlockingTable
deriving FromJson, ToJson, Repr

def WireNodePair.natPair (pair : WireNodePair) : Nat × Nat :=
  (pair.source, pair.target)

def WireEqProductionBlockingTable.forbiddenNat
    (wire : WireEqProductionBlockingTable) : Finset (Nat × Nat) :=
  (wire.forbidden.map WireNodePair.natPair).toFinset

def WireEqProductionBlockingTable.optionPairsNat
    (wire : WireEqProductionBlockingTable) : Finset (Nat × Nat) :=
  (wire.options.flatMap fun option =>
    option.blockers.map fun blocker => (option.source, blocker)).toFinset

def WireEqProductionBlockingTable.accepted
    (wire : WireEqProductionBlockingTable) : Bool :=
  match wire.check with
  | .ok true => true
  | _ => false

def WireEqProductionBlockingTable.sameProblem
    (left right : WireEqProductionBlockingTable) : Bool :=
  left.base.node_count == right.base.node_count &&
    left.base.concept_count == right.base.concept_count &&
    left.base.role_count == right.base.role_count &&
    left.base.variable_count == right.base.variable_count &&
    toJson left.base.ontology == toJson right.base.ontology &&
    left.all_blockable_sources == right.all_blockable_sources &&
    left.validate_rejections == right.validate_rejections &&
    toJson left.definitions == toJson right.definitions &&
    toJson left.exact_definitions == toJson right.exact_definitions &&
    toJson left.native_seed == toJson right.native_seed

def WireEqProductionBlockingTable.nextForbiddenExact
    (current next : WireEqProductionBlockingTable) : Bool :=
  next.forbiddenNat == current.forbiddenNat ∪ current.optionPairsNat

def WireEqProductionExecutionTrace.transitionsValid :
    List WireEqProductionBlockingTable → Bool
  | [] | [_] => true
  | current :: next :: rest =>
      current.sameProblem next && current.nextForbiddenExact next &&
        transitionsValid (next :: rest)

def WireEqProductionExecutionTrace.check
    (wire : WireEqProductionExecutionTrace) : Bool :=
  wire.version == 1 &&
    match wire.rounds with
    | [] => false
    | first :: _ =>
        wire.rounds.all WireEqProductionBlockingTable.accepted &&
          decide (first.forbiddenNat = ∅) &&
          WireEqProductionExecutionTrace.transitionsValid wire.rounds

theorem WireEqProductionBlockingTable.accepted_eq_true_iff
    (wire : WireEqProductionBlockingTable) :
    wire.accepted = true ↔ wire.check = .ok true := by
  unfold WireEqProductionBlockingTable.accepted
  cases hcheck : wire.check <;> simp
  rename_i value
  cases value <;> simp

theorem WireEqProductionExecutionTrace.check_all_rounds
    (wire : WireEqProductionExecutionTrace)
    (hcheck : wire.check = true) :
    ∀ round ∈ wire.rounds, round.check = .ok true := by
  unfold WireEqProductionExecutionTrace.check at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i first rest heq
    simp only [Bool.and_eq_true] at hcheck
    intro round hround
    exact round.accepted_eq_true_iff.mp
      ((List.all_eq_true.mp hcheck.2.1.1) round hround)

theorem WireEqProductionExecutionTrace.check_starts_empty
    (wire : WireEqProductionExecutionTrace)
    (hcheck : wire.check = true) :
    ∃ first rest, wire.rounds = first :: rest ∧ first.forbiddenNat = ∅ := by
  unfold WireEqProductionExecutionTrace.check at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i first rest heq
    simp only [Bool.and_eq_true] at hcheck
    refine ⟨first, rest, heq, ?_⟩
    exact of_decide_eq_true hcheck.2.1.2

theorem WireEqProductionExecutionTrace.transitionsValid_head
    {current next : WireEqProductionBlockingTable}
    {rest : List WireEqProductionBlockingTable}
    (hvalid : WireEqProductionExecutionTrace.transitionsValid
      (current :: next :: rest) = true) :
    current.sameProblem next = true ∧
      current.nextForbiddenExact next = true ∧
      WireEqProductionExecutionTrace.transitionsValid (next :: rest) = true := by
  simp only [WireEqProductionExecutionTrace.transitionsValid,
    Bool.and_eq_true] at hvalid
  exact ⟨hvalid.1.1, hvalid.1.2, hvalid.2⟩

/-- Every adjacent checked rerun starts from exactly the pair-set union learned
by its predecessor and retains the same source problem metadata. -/
theorem WireEqProductionExecutionTrace.check_first_transition
    (wire : WireEqProductionExecutionTrace)
    {current next : WireEqProductionBlockingTable}
    {rest : List WireEqProductionBlockingTable}
    (hrounds : wire.rounds = current :: next :: rest)
    (hcheck : wire.check = true) :
    current.sameProblem next = true ∧
      next.forbiddenNat = current.forbiddenNat ∪ current.optionPairsNat := by
  unfold WireEqProductionExecutionTrace.check at hcheck
  rw [hrounds] at hcheck
  simp only [Bool.and_eq_true] at hcheck
  have htransition :=
    WireEqProductionExecutionTrace.transitionsValid_head hcheck.2.2
  exact ⟨htransition.1, beq_iff_eq.mp htransition.2.1⟩

#print axioms WireEqProductionExecutionTrace.check_all_rounds
#print axioms WireEqProductionExecutionTrace.check_starts_empty
#print axioms WireEqProductionExecutionTrace.check_first_transition

end ContextCalculus.Hypertableau
