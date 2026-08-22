import ContextCalculus.HypertableauRegularProduction

/-!
# Total blocker-assignment and forced-expansion production control

The fixed-budget production loop has two finite learning layers.  It first
rejects complete simultaneous blocker assignments.  Once that Cartesian
product is exhausted, it reruns saturation while forbidding every blocker pair
exposed by the exhausted state.  This module prevents the second transition
from being hidden behind an arbitrary result-valued continuation: every
expansion must exhibit at least one pair not already forbidden.
-/

namespace ContextCalculus.Hypertableau

/-- Result of one settled inner assignment loop at a fixed outer forbidden-pair
set.  `expand` is constructor-guarded by strict growth of that outer set. -/
inductive GuardedFoldExpansionOutcome (Node Result : Type)
    [DecidableEq Node]
    (forbidden : Finset (Node × Node)) where
  | done (result : Result)
  | expand (pairs : Finset (Node × Node))
      (fresh : ∃ pair ∈ pairs, pair ∉ forbidden)

/-- Lift an ordinary optional checked candidate into the expansion runtime.
Acceptance is definitionally conclusive; rejection carries no semantic result.
-/
def checkedFoldCandidate [DecidableEq Node]
    (candidate : Finset (FoldAssignment Node) → FoldAssignment Node →
      Option Result)
    (forbidden : Finset (Node × Node))
    (rejected : Finset (FoldAssignment Node))
    (assignment : FoldAssignment Node) :
    GuardedFoldExpansionOutcome Node Result forbidden ⊕ Unit :=
  match candidate rejected assignment with
  | some result => .inl (.done result)
  | none => .inr ()

theorem checkedFoldCandidate_conclusive [DecidableEq Node]
    (candidate : Finset (FoldAssignment Node) → FoldAssignment Node →
      Option Result)
    (forbidden : Finset (Node × Node))
    (rejected : Finset (FoldAssignment Node))
    (assignment : FoldAssignment Node)
    (outcome : GuardedFoldExpansionOutcome Node Result forbidden)
    (hcheck : checkedFoldCandidate candidate forbidden rejected assignment =
      .inl outcome) :
    ∃ result, outcome = .done result := by
  cases hcandidate : candidate rejected assignment with
  | none => simp [checkedFoldCandidate, hcandidate] at hcheck
  | some result =>
      have heq : GuardedFoldExpansionOutcome.done result = outcome := by
        simpa [checkedFoldCandidate, hcandidate] using hcheck
      exact ⟨result, heq.symm⟩

/-- A nonempty source-major option table whose blocker lists are nonempty and
already filtered against the current forbidden set exposes a fresh outer pair.
-/
theorem foldOptionPairs_has_fresh_of_filtered [DecidableEq Node]
    {forbidden : Finset (Node × Node)}
    {options : List (Node × List Node)}
    (hne : options ≠ [])
    (hnonempty : ∀ option ∈ options, option.2 ≠ [])
    (hfiltered : ∀ source blockers,
      (source, blockers) ∈ options →
      ∀ blocker ∈ blockers, (source, blocker) ∉ forbidden) :
    ∃ pair ∈ foldOptionPairs options, pair ∉ forbidden := by
  obtain ⟨option, hoption⟩ := List.exists_mem_of_ne_nil options hne
  obtain ⟨blocker, hblocker⟩ := List.exists_mem_of_ne_nil option.2
    (hnonempty option hoption)
  refine ⟨(option.1, blocker), ?_, hfiltered option.1 option.2 hoption blocker
    hblocker⟩
  exact mem_foldOptionPairs_iff.mpr ⟨option.2, hoption, hblocker⟩

/-- Exact two-level fixed-budget control shape used by KM.  Each outer attempt
is an executable complete-assignment runtime.  Its accepted candidate can
finish with `done`; exact assignment exhaustion can request a rerun only by
returning a guarded, strictly growing pair set. -/
structure CartesianFoldExpansionRuntime (Node Result : Type)
    [DecidableEq Node] where
  inner : ∀ forbidden : Finset (Node × Node),
    CartesianFoldAssignmentRuntime Node
      (GuardedFoldExpansionOutcome Node Result forbidden)
  checkConclusive : ∀ forbidden rejected assignment outcome,
    (inner forbidden).check rejected assignment = .inl outcome →
      ∃ result, outcome = .done result
  expansionExact : ∀ forbidden rejected exhausted pairs fresh,
    (inner forbidden).onExhausted rejected exhausted = .expand pairs fresh →
      pairs = foldOptionPairs ((inner forbidden).options rejected)

/-- Select the terminating outcome of the finite inner Cartesian loop.  The
selected retry remains an implementation detail; its existence is supplied by
the executable first-fresh assignment theorem. -/
noncomputable def CartesianFoldExpansionRuntime.settled
    [Fintype Node] [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result)
    (forbidden : Finset (Node × Node)) :
    GuardedFoldExpansionOutcome Node Result forbidden := by
  let witness : Nonempty { selected :
      Nat × GuardedFoldExpansionOutcome Node Result forbidden //
    (runtime.inner forbidden).toProducer.toGuarded.toFoldAssignmentProducer.run
        selected.1 = .done selected.2 } := by
    rcases (runtime.inner forbidden).eventually_done with
      ⟨retry, outcome, hrun⟩
    exact ⟨⟨(retry, outcome), hrun⟩⟩
  exact (Classical.choice witness).1.2

/-- Erase the nested executable assignment loop into the already proved
strict-growth producer for forbidden pairs. -/
noncomputable def CartesianFoldExpansionRuntime.toGuardedFoldProducer
    [Fintype Node] [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result) :
    GuardedFoldProducer Node Result where
  attempt forbidden :=
    match runtime.settled forbidden with
    | .done result => .done result
    | .expand pairs fresh => .rejected pairs fresh

/-- Both learning layers terminate at every finite node budget.  In
particular, a production route cannot claim completeness if exhausted blocker
assignments lead to a rerun that adds no new forbidden pair. -/
theorem CartesianFoldExpansionRuntime.eventually_done
    [Fintype Node] [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result) :
    ∃ round result,
      runtime.toGuardedFoldProducer.toFreshFoldProducer.run round =
        .done result :=
  runtime.toGuardedFoldProducer.toFreshFoldProducer.eventually_done

theorem CartesianFoldExpansionRuntime.expansion_strict
    [Fintype Node] [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result)
    {forbidden pairs : Finset (Node × Node)}
    {fresh : ∃ pair ∈ pairs, pair ∉ forbidden}
    (hsettled : runtime.settled forbidden = .expand pairs fresh) :
    forbidden ⊂ forbidden ∪ pairs := by
  rcases fresh with ⟨pair, hpairs, hfresh⟩
  exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, by
    intro heq
    have : pair ∈ forbidden := by
      rw [heq]
      exact Finset.mem_union_right forbidden hpairs
    exact hfresh this⟩

theorem CartesianFoldExpansionRuntime.accepted_candidate_conclusive
    [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result)
    {forbidden : Finset (Node × Node)}
    {rejected : Finset (FoldAssignment Node)}
    {assignment : FoldAssignment Node}
    {outcome : GuardedFoldExpansionOutcome Node Result forbidden}
    (hcheck : (runtime.inner forbidden).check rejected assignment =
      .inl outcome) :
    ∃ result, outcome = .done result :=
  runtime.checkConclusive forbidden rejected assignment outcome hcheck

theorem CartesianFoldExpansionRuntime.exhausted_pairs_exact
    [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result)
    {forbidden : Finset (Node × Node)}
    {rejected : Finset (FoldAssignment Node)}
    {exhausted : ∀ assignment ∈ enumerateFoldAssignments
      ((runtime.inner forbidden).options rejected), assignment ∈ rejected}
    {pairs : Finset (Node × Node)}
    {fresh : ∃ pair ∈ pairs, pair ∉ forbidden}
    (hexhausted : (runtime.inner forbidden).onExhausted rejected exhausted =
      .expand pairs fresh) :
    pairs = foldOptionPairs ((runtime.inner forbidden).options rejected) :=
  runtime.expansionExact forbidden rejected exhausted pairs fresh hexhausted

#print axioms CartesianFoldExpansionRuntime.eventually_done
#print axioms checkedFoldCandidate_conclusive
#print axioms foldOptionPairs_has_fresh_of_filtered
#print axioms CartesianFoldExpansionRuntime.expansion_strict
#print axioms CartesianFoldExpansionRuntime.accepted_candidate_conclusive
#print axioms CartesianFoldExpansionRuntime.exhausted_pairs_exact

end ContextCalculus.Hypertableau
