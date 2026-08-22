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

/-! ### Concrete execution traces

The totality theorem above the production boundary used to retain only the
function which *could* perform the finite retry loop.  The following indexed
trace records the loop which was actually performed.  Its three constructors
are exactly Rust's branches: accept the first fresh assignment, reject that
exact assignment and continue after inserting it, or invoke the exhaustion
continuation only after `firstFreshFoldAssignment` returns `none`.

Unlike `eventually_done`, this trace contains no selected witness and uses no
classical choice.  It is therefore suitable as the semantic target of the
wire decoder for a concrete KM execution.
-/

inductive CartesianFoldAssignmentExecution
    [DecidableEq Node]
    (runtime : CartesianFoldAssignmentRuntime Node Result) :
    Finset (FoldAssignment Node) → Result → Type where
  | accepted
      (rejected : Finset (FoldAssignment Node))
      (assignment : FoldAssignment Node)
      (result : Result)
      (selected : firstFreshFoldAssignment rejected
        (enumerateFoldAssignments (runtime.options rejected)) = some assignment)
      (checked : runtime.check rejected assignment = .inl result) :
      CartesianFoldAssignmentExecution runtime rejected result
  | rejected
      (rejected : Finset (FoldAssignment Node))
      (assignment : FoldAssignment Node)
      (result : Result)
      (selected : firstFreshFoldAssignment rejected
        (enumerateFoldAssignments (runtime.options rejected)) = some assignment)
      (checked : runtime.check rejected assignment = .inr ())
      (next : CartesianFoldAssignmentExecution runtime
        (insert assignment rejected) result) :
      CartesianFoldAssignmentExecution runtime rejected result
  | exhausted
      (rejected : Finset (FoldAssignment Node))
      (selected : firstFreshFoldAssignment rejected
        (enumerateFoldAssignments (runtime.options rejected)) = none) :
      CartesianFoldAssignmentExecution runtime rejected
        (runtime.onExhausted rejected
          ((firstFreshFoldAssignment_eq_none_iff rejected
            (enumerateFoldAssignments (runtime.options rejected))).mp selected))

def CartesianFoldAssignmentExecution.steps
    [DecidableEq Node]
    {runtime : CartesianFoldAssignmentRuntime Node Result}
    {rejected : Finset (FoldAssignment Node)} {result : Result} :
    CartesianFoldAssignmentExecution runtime rejected result → Nat
  | .accepted .. => 0
  | .rejected _ _ _ _ _ next => next.steps + 1
  | .exhausted .. => 0

/-- The exact nested fixed-budget trace.  Every outer expansion is justified
by complete inner assignment execution and carries the constructor-level fresh
pair proof required by `GuardedFoldExpansionOutcome.expand`. -/
inductive CartesianFoldExpansionExecution
    [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result) :
    Finset (Node × Node) → Result → Type where
  | done
      (forbidden : Finset (Node × Node))
      (result : Result)
      (inner : CartesianFoldAssignmentExecution (runtime.inner forbidden) ∅
        (.done result)) :
      CartesianFoldExpansionExecution runtime forbidden result
  | expand
      (forbidden pairs : Finset (Node × Node))
      (fresh : ∃ pair ∈ pairs, pair ∉ forbidden)
      (result : Result)
      (inner : CartesianFoldAssignmentExecution (runtime.inner forbidden) ∅
        (.expand pairs fresh))
      (next : CartesianFoldExpansionExecution runtime
        (forbidden ∪ pairs) result) :
      CartesianFoldExpansionExecution runtime forbidden result

/-- An outer expansion recorded by a concrete trace cannot have come from an
accepted candidate.  It is necessarily the exhaustion continuation, and the
learned pair set is exactly the union of the options exposed by that terminal
state. -/
theorem CartesianFoldAssignmentExecution.expand_exact
    [DecidableEq Node]
    (runtime : CartesianFoldExpansionRuntime Node Result)
    (forbidden pairs : Finset (Node × Node))
    (fresh : ∃ pair ∈ pairs, pair ∉ forbidden)
    (initial : Finset (FoldAssignment Node))
    {outcome : GuardedFoldExpansionOutcome Node Result forbidden}
    (trace : CartesianFoldAssignmentExecution (runtime.inner forbidden) initial
      outcome)
    (houtcome : outcome = .expand pairs fresh) :
    ∃ rejected, ∃ exhausted : ∀ assignment ∈ enumerateFoldAssignments
          ((runtime.inner forbidden).options rejected), assignment ∈ rejected,
      (runtime.inner forbidden).onExhausted rejected exhausted =
          .expand pairs fresh ∧
        pairs = foldOptionPairs ((runtime.inner forbidden).options rejected) := by
  induction trace with
  | accepted rejected assignment outcome selected checked =>
      subst outcome
      obtain ⟨result, hdone⟩ :=
        runtime.checkConclusive forbidden rejected assignment
          (.expand pairs fresh) checked
      cases hdone
  | rejected rejected assignment outcome selected checked next ih =>
      exact ih houtcome
  | exhausted rejected selected =>
      let exhausted :=
        (firstFreshFoldAssignment_eq_none_iff rejected
          (enumerateFoldAssignments
            ((runtime.inner forbidden).options rejected))).mp selected
      refine ⟨rejected, exhausted, houtcome, ?_⟩
      exact runtime.expansionExact forbidden rejected exhausted pairs fresh houtcome

theorem CartesianFoldExpansionExecution.inner_settles
    [DecidableEq Node]
    {runtime : CartesianFoldExpansionRuntime Node Result}
    {forbidden : Finset (Node × Node)} {result : Result}
    (trace : CartesianFoldExpansionExecution runtime forbidden result) :
    Nonempty (Σ outcome,
      CartesianFoldAssignmentExecution (runtime.inner forbidden) ∅ outcome) := by
  cases trace with
  | done _ _ inner => exact ⟨⟨_, inner⟩⟩
  | expand _ _ _ _ inner _ => exact ⟨⟨_, inner⟩⟩

/-- Every expansion step in a concrete outer trace is backed by an exhausted
Cartesian product whose exact option-pair union is learned. -/
theorem CartesianFoldExpansionExecution.head_expansion_exact
    [DecidableEq Node]
    {runtime : CartesianFoldExpansionRuntime Node Result}
    {forbidden pairs : Finset (Node × Node)}
    {fresh : ∃ pair ∈ pairs, pair ∉ forbidden}
    {result : Result}
    (trace : CartesianFoldExpansionExecution runtime forbidden result)
    (hhead : ∃ inner next, trace = .expand forbidden pairs fresh result inner next) :
    ∃ rejected, ∃ _exhausted : ∀ assignment ∈ enumerateFoldAssignments
          ((runtime.inner forbidden).options rejected), assignment ∈ rejected,
      pairs = foldOptionPairs ((runtime.inner forbidden).options rejected) := by
  rcases hhead with ⟨inner, next, rfl⟩
  obtain ⟨rejected, exhausted, _, hexact⟩ :=
    inner.expand_exact runtime forbidden pairs fresh ∅ rfl
  exact ⟨rejected, exhausted, hexact⟩

/-! ### Concrete frontier-doubling traces

The production decision loop has one further layer above fixed-budget fold
learning.  A checked frontier advances from `budget` to `budget + 1`; any
conclusive checked outcome ends the run.  Keeping the node type indexed by the
budget makes the `8 * 2^budget` schedule part of the trace type rather than an
untrusted integer supplied by the producer.
-/

inductive CartesianFoldDoublingExecution
    (Result : Type)
    (runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget)) Result)
    (Frontier : Nat → Result → Prop)
    (Conclusive : Result → Prop) : Nat → Result → Type where
  | done
      (budget : Nat)
      (outcome : Result)
      (fixed : CartesianFoldExpansionExecution (runtime budget) ∅ outcome)
      (conclusive : Conclusive outcome) :
      CartesianFoldDoublingExecution Result runtime Frontier Conclusive
        budget outcome
  | deepen
      (budget : Nat)
      (frontier : Result)
      (final : Result)
      (fixed : CartesianFoldExpansionExecution (runtime budget) ∅ frontier)
      (checkedFrontier : Frontier budget frontier)
      (next : CartesianFoldDoublingExecution Result runtime Frontier Conclusive
        (budget + 1) final) :
      CartesianFoldDoublingExecution Result runtime Frontier Conclusive
        budget final

def CartesianFoldDoublingExecution.frontierSteps
    {runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget)) Result}
    {Frontier : Nat → Result → Prop}
    {Conclusive : Result → Prop}
    {budget : Nat} {result : Result} :
    CartesianFoldDoublingExecution Result runtime Frontier Conclusive
      budget result → Nat
  | .done .. => 0
  | .deepen _ _ _ _ _ next => next.frontierSteps + 1

/-- A complete concrete doubling trace ends in the conclusive predicate
carried by its terminal checked outcome. -/
theorem CartesianFoldDoublingExecution.conclusive
    {runtime : ∀ budget, CartesianFoldExpansionRuntime
      (Fin (8 * 2 ^ budget)) Result}
    {Frontier : Nat → Result → Prop}
    {Conclusive : Result → Prop}
    {budget : Nat} {result : Result}
    (trace : CartesianFoldDoublingExecution Result runtime Frontier Conclusive
      budget result) :
    Conclusive result := by
  induction trace with
  | done _ _ _ hconclusive => exact hconclusive
  | deepen _ _ _ _ _ _ ih => exact ih

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
#print axioms CartesianFoldExpansionExecution.inner_settles
#print axioms CartesianFoldAssignmentExecution.expand_exact
#print axioms CartesianFoldExpansionExecution.head_expansion_exact
#print axioms CartesianFoldDoublingExecution.conclusive

end ContextCalculus.Hypertableau
