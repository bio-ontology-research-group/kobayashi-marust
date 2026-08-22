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

/-! ## Canonical finite certificate for a concrete terminal state -/

noncomputable def FiniteSatCertificate.ofState
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] :
    FiniteSatCertificate nodeCount conceptCount roleCount variableCount := by
  classical
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  exact {
    ontology := ontology
    labels := (Finset.univ.filter fun entry : Fin nodeCount × Lit (Fin conceptCount) =>
      state.label entry.1 entry.2).toList
    edges := (Finset.univ.filter fun entry :
        Fin roleCount × Fin nodeCount × Fin nodeCount =>
      state.edge entry.1 entry.2.1 entry.2.2).toList
    obligations := (Finset.univ.filter fun entry :
        Fin roleCount × Lit (Fin conceptCount) × Fin nodeCount =>
      state.obligation entry.1 entry.2.1 entry.2.2).toList }

theorem FiniteSatCertificate.ofState_state
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state] :
    (FiniteSatCertificate.ofState ontology state).state = state := by
  apply State.ext <;> funext
  · simp [FiniteSatCertificate.ofState, FiniteSatCertificate.state]
  · simp [FiniteSatCertificate.ofState, FiniteSatCertificate.state]
  · simp [FiniteSatCertificate.ofState, FiniteSatCertificate.state]

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

theorem State.productionUnwitnessedSources_eq_nil_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state] :
    state.productionUnwitnessedSources = [] ↔ ¬state.HasUnwitnessed := by
  constructor
  · intro hempty hunwitnessed
    rcases hunwitnessed with
      ⟨source, role, filler, hobligation, hnowitness⟩
    have hmem : source ∈ state.productionUnwitnessedSources :=
      (state.mem_productionUnwitnessedSources_iff source).mpr
        ⟨role, filler, hobligation, hnowitness⟩
    simp [hempty] at hmem
  · intro hnone
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro source hsource
    rcases (state.mem_productionUnwitnessedSources_iff source).mp hsource with
      ⟨role, filler, hobligation, hnowitness⟩
    exact hnone ⟨source, role, filler, hobligation, hnowitness⟩

/-- If production exposes no blocked source, the blocker-aware terminal is an
ordinary finite terminal. Lean enumerates the exact state and proves that its
finite SAT checker accepts; no serializer-completeness premise is required. -/
theorem FiniteSatCertificate.checkSat_of_empty_production_terminal
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (state : State (Fin nodeCount) (Fin conceptCount) (Fin roleCount))
    [DecidableState state]
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (forbidden : Finset (Fin nodeCount × Fin nodeCount))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hterminal : state.BlockedRuntimeTerminal ontology
      (state.productionBlocked parent ancestors forbidden))
    (hempty : state.productionUnwitnessedSources = []) :
    (FiniteSatCertificate.ofState ontology state).checkSat = true := by
  apply FiniteSatCertificate.checkSat_complete
  refine ⟨hguarded, ?_, ?_, ?_⟩
  · rw [FiniteSatCertificate.ofState_state]
    exact hterminal.clashFree
  · intro obligation hobligation
    have hnowitness :=
      (state.productionUnwitnessedSources_eq_nil_iff.mp hempty)
    have hwitness :
        (FiniteSatCertificate.ofState ontology state).state.WitnessComplete := by
      rw [FiniteSatCertificate.ofState_state]
      exact state.witnessComplete_of_noUnwitnessed hnowitness
    exact hwitness obligation.2.2 obligation.1 obligation.2.1 hobligation
  · rw [FiniteSatCertificate.ofState_state]
    exact hterminal.saturatedFor

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
#print axioms FiniteSatCertificate.ofState_state
#print axioms State.productionBlocked_foldTotal
#print axioms State.mem_productionUnwitnessedSources_iff
#print axioms State.productionUnwitnessedSources_eq_nil_iff
#print axioms FiniteSatCertificate.checkSat_of_empty_production_terminal
#print axioms State.productionTerminal_sources_blocked
#print axioms State.productionTerminal_foldTable

end ContextCalculus.Hypertableau
