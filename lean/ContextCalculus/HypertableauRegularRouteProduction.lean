import ContextCalculus.HypertableauExpansionProduction
import ContextCalculus.HypertableauRoleBlocking

/-!
# Concrete equality-free blocker options for production HT

This module reconstructs the blocker table exposed by Rust's equality-free
open leaf.  Sources are exactly nodes with an unwitnessed obligation.  Their
options are the non-forbidden ancestors with the same complete pairwise
blocking signature.  Consequently an open blocker-aware runtime terminal
supplies the total fold table required by the executable Cartesian assignment
producer; callers do not assert option non-emptiness separately.
-/

namespace ContextCalculus.Hypertableau

noncomputable def State.productionFold
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    [DecidableEq Node]
    (state : State Node Concept Role)
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    (source blocker : Node) : Prop :=
  blocker ∈ ancestors source ∧
    state.roleBlockingSignature parent blocker =
      state.roleBlockingSignature parent source ∧
    (source, blocker) ∉ forbidden

noncomputable def State.productionBlocked
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    [DecidableEq Node]
    (state : State Node Concept Role)
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    (source : Node) : Bool := by
  classical
  exact decide
    (∃ blocker, state.productionFold parent ancestors forbidden source blocker)

theorem State.productionBlocked_eq_true_iff
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    [DecidableEq Node]
    (state : State Node Concept Role)
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    (source : Node) :
    state.productionBlocked parent ancestors forbidden source = true ↔
      ∃ blocker, state.productionFold parent ancestors forbidden source blocker := by
  simp [State.productionBlocked]

theorem State.productionBlocked_foldTotal
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    [DecidableEq Node]
    (state : State Node Concept Role)
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node)) :
    State.BlockedFoldTotal
      (state.productionBlocked parent ancestors forbidden)
      (state.productionFold parent ancestors forbidden) := by
  intro source hblocked
  exact (state.productionBlocked_eq_true_iff parent ancestors forbidden source).mp
    hblocked

noncomputable def State.productionUnwitnessedSources
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state] : List Node :=
  by
    classical
    exact Finset.univ.filter (fun source =>
      ∃ role filler, state.obligation role filler source ∧
        ∀ witness, ¬(state.edge role source witness ∧ state.label witness filler))
      |>.toList

theorem State.mem_productionUnwitnessedSources_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (source : Node) :
    source ∈ state.productionUnwitnessedSources ↔
      ∃ role filler, state.obligation role filler source ∧
        ∀ witness,
          ¬(state.edge role source witness ∧ state.label witness filler) := by
  classical
  simp [State.productionUnwitnessedSources]

theorem State.productionTerminal_sources_blocked
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (ontology : List (Clause Variable Concept Role))
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    (hterminal : state.BlockedRuntimeTerminal ontology
      (state.productionBlocked parent ancestors forbidden))
    (source : Node)
    (hsource : source ∈ state.productionUnwitnessedSources) :
    state.productionBlocked parent ancestors forbidden source = true := by
  rcases (state.mem_productionUnwitnessedSources_iff source).mp hsource with
    ⟨role, filler, hobligation, hnowitness⟩
  exact State.BlockedRuntimeTerminal.unwitnessed_is_blocked state ontology
    (state.productionBlocked parent ancestors forbidden) hterminal source role
    filler hobligation hnowitness

/-- The exact fold-table ingredients of an equality-free blocked terminal.
`CartesianFoldAssignmentRuntime.ofFoldTable` can consume these three results
directly for every rejected-assignment state. -/
theorem State.productionTerminal_foldTable
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (ontology : List (Clause Variable Concept Role))
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    (hterminal : state.BlockedRuntimeTerminal ontology
      (state.productionBlocked parent ancestors forbidden)) :
    State.BlockedFoldTotal
        (state.productionBlocked parent ancestors forbidden)
        (state.productionFold parent ancestors forbidden) ∧
      ∀ source ∈ state.productionUnwitnessedSources,
        state.productionBlocked parent ancestors forbidden source = true := by
  exact ⟨state.productionBlocked_foldTotal parent ancestors forbidden,
    state.productionTerminal_sources_blocked ontology parent ancestors forbidden
      hterminal⟩

/-- Construct the complete inner assignment runtime from one concrete
equality-free blocked terminal.  The options are fixed for that saturated leaf,
as in Rust; only the rejected complete-assignment set changes between retries.
The terminal theorem derives both fold totality and source option non-emptiness.
-/
noncomputable def CartesianFoldAssignmentRuntime.ofProductionTerminal
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (ontology : List (Clause Variable Concept Role))
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    (hterminal : state.BlockedRuntimeTerminal ontology
      (state.productionBlocked parent ancestors forbidden))
    (check : Finset (FoldAssignment Node) → FoldAssignment Node →
      Result ⊕ Unit)
    (onExhausted : ∀ rejected : Finset (FoldAssignment Node),
      (∀ assignment ∈ enumerateFoldAssignments
        (foldOptionsUsing
          (state.productionFold parent ancestors forbidden)
          (Classical.decRel
            (state.productionFold parent ancestors forbidden))
          state.productionUnwitnessedSources), assignment ∈ rejected) → Result) :
    CartesianFoldAssignmentRuntime Node Result := by
  classical
  exact CartesianFoldAssignmentRuntime.ofFoldTable
    (fun _ => state.productionBlocked parent ancestors forbidden)
    (fun _ => state.productionFold parent ancestors forbidden)
    (fun _ => Classical.decRel
      (state.productionFold parent ancestors forbidden))
    (fun _ => state.productionBlocked_foldTotal parent ancestors forbidden)
    (fun _ => state.productionUnwitnessedSources)
    (fun _ source hsource =>
      state.productionTerminal_sources_blocked ontology parent ancestors forbidden
        hterminal source hsource)
    check onExhausted

#print axioms State.productionBlocked_eq_true_iff
#print axioms State.productionBlocked_foldTotal
#print axioms State.mem_productionUnwitnessedSources_iff
#print axioms State.productionTerminal_sources_blocked
#print axioms State.productionTerminal_foldTable

end ContextCalculus.Hypertableau
