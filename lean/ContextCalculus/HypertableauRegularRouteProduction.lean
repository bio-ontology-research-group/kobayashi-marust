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

/-! ## Executable finite production blocking table -/

def ancestorChain (parent : Node → Option Node) : Nat → Node → List Node
  | 0, _ => []
  | fuel + 1, node =>
      match parent node with
      | none => []
      | some predecessor => predecessor :: ancestorChain parent fuel predecessor

structure FiniteProductionBlockingTable
    (nodeCount conceptCount roleCount variableCount : Nat) where
  base : FiniteSatCertificate nodeCount conceptCount roleCount variableCount
  parent : Fin nodeCount → Option (Fin nodeCount)
  forbidden : Finset (Fin nodeCount × Fin nodeCount)
  options : List (Fin nodeCount × List (Fin nodeCount))

instance FiniteSatCertificate.decidableState
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    DecidableState certificate.state where
  label := fun node literal => by
    change Decidable ((node, literal) ∈ certificate.labels)
    infer_instance
  edge := fun role source target => by
    change Decidable ((role, source, target) ∈ certificate.edges)
    infer_instance
  obligation := fun role filler node => by
    change Decidable ((role, filler, node) ∈ certificate.obligations)
    infer_instance

/-! ## Concrete recursive production search -/

noncomputable def productionBlockedFacts
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (parent : Finset (GuardedFact Node Concept Role) → Node → Option Node)
    (ancestors : Finset (GuardedFact Node Concept Role) → Node → List Node)
    (forbidden : Finset (Node × Node))
    (facts : Finset (GuardedFact Node Concept Role)) (source : Node) : Bool :=
  (stateOfGuardedFacts facts).productionBlocked (parent facts)
    (ancestors facts) forbidden source

/-- Instantiate the exhaustive blocker-aware recursion theorem with KM's exact
production blocker predicate. Every fixed-budget run is therefore a refutation
or descends to a concretely classified production terminal/frontier; no
abstract successor or terminal producer remains in this recursion layer. -/
theorem finite_productionBlocked_terminal_or_frontier
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → List (Fin nodeCount))
    (forbidden : Finset (Fin nodeCount × Fin nodeCount))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom) :
    ∀ root,
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) ∨
      ∃ leaf, SearchDescends
          (runtimeNextBlockedFacts ontology
            (productionBlockedFacts parent ancestors forbidden)) root leaf ∧
        ((stateOfGuardedFacts leaf).BlockedRuntimeTerminal ontology
            ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
              (ancestors leaf) forbidden) ∨
          (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
            ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
              (ancestors leaf) forbidden)) := by
  exact finite_runtimeNextBlocked_terminal_or_frontier ontology
    (productionBlockedFacts parent ancestors forbidden) hheads

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

theorem State.productionFold_not_forbidden
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    [DecidableEq Node]
    (state : State Node Concept Role)
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node))
    {source blocker : Node}
    (hfold : state.productionFold parent ancestors forbidden source blocker) :
    (source, blocker) ∉ forbidden :=
  hfold.2.2

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

noncomputable def FiniteProductionBlockingTable.expectedOptions
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    List (Fin nodeCount × List (Fin nodeCount)) := by
  classical
  exact (List.finRange nodeCount).filter (fun source => decide
      (∃ role filler, table.base.state.obligation role filler source ∧
        ∀ witness, ¬(table.base.state.edge role source witness ∧
          table.base.state.label witness filler)))
    |>.map fun source =>
      (source, (ancestorChain table.parent nodeCount source).filter fun blocker => decide
        (table.base.state.productionFold table.parent
          (ancestorChain table.parent nodeCount) table.forbidden source blocker))

/-- Executable exactness check for the fold-option table emitted by
production. It does not establish that the parent map came from recursive
search; that separate transition invariant is the next refinement layer. -/
noncomputable def FiniteProductionBlockingTable.checkOptions
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    Bool := by
  classical
  exact decide (table.options = table.expectedOptions)

theorem FiniteProductionBlockingTable.checkOptions_eq_true_iff
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    table.checkOptions = true ↔ table.options = table.expectedOptions := by
  classical
  simp [FiniteProductionBlockingTable.checkOptions]

theorem FiniteProductionBlockingTable.checked_option_exact
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount)
    (hcheck : table.checkOptions = true) :
    table.options = table.expectedOptions :=
  table.checkOptions_eq_true_iff.mp hcheck

theorem FiniteProductionBlockingTable.checked_pairs_exact
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount)
    (hcheck : table.checkOptions = true) :
    foldOptionPairs table.options = foldOptionPairs table.expectedOptions := by
  rw [table.checked_option_exact hcheck]

def FiniteProductionBlockingTable.ParentEarlier
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    Prop :=
  ∀ node predecessor, table.parent node = some predecessor → predecessor.val < node.val

noncomputable def FiniteProductionBlockingTable.parentEarlierB
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    Bool :=
  (Finset.univ.toList : List (Fin nodeCount)).all fun node =>
    match table.parent node with
    | none => true
    | some predecessor => decide (predecessor.val < node.val)

theorem FiniteProductionBlockingTable.parentEarlierB_eq_true_iff
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    table.parentEarlierB = true ↔ table.ParentEarlier := by
  classical
  simp only [FiniteProductionBlockingTable.parentEarlierB, List.all_eq_true,
    Finset.mem_toList, Finset.mem_univ, true_implies]
  constructor
  · intro hall node predecessor hparent
    have hnode := hall node
    rw [hparent] at hnode
    simpa using hnode
  · intro hearlier node
    cases hparent : table.parent node with
    | none => simp
    | some predecessor =>
        simpa using hearlier node predecessor hparent

/-- Combined production-control check. Earlier-parent validation makes the
fuel-bounded ancestor reconstruction faithful to Rust's predecessor forest;
option equality then checks the entire source-major blocker table. -/
noncomputable def FiniteProductionBlockingTable.check
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    Bool :=
  table.parentEarlierB && table.checkOptions

theorem FiniteProductionBlockingTable.check_eq_true_iff
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount) :
    table.check = true ↔ table.ParentEarlier ∧
      table.options = table.expectedOptions := by
  classical
  simp [FiniteProductionBlockingTable.check,
    FiniteProductionBlockingTable.parentEarlierB_eq_true_iff,
    FiniteProductionBlockingTable.checkOptions_eq_true_iff]

theorem FiniteProductionBlockingTable.check_sound
    (table : FiniteProductionBlockingTable nodeCount conceptCount roleCount variableCount)
    (hcheck : table.check = true) :
    table.ParentEarlier ∧ table.options = table.expectedOptions :=
  table.check_eq_true_iff.mp hcheck

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

/-- The concrete recursive production search separates all fixed-budget leaf
meanings needed by the outer controller. A fold-free terminal already carries
an accepted exact finite certificate; only a terminal with a nonempty blocked
source table proceeds to Cartesian fold learning. -/
theorem finite_productionBlocked_checked_leaf
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → List (Fin nodeCount))
    (forbidden : Finset (Fin nodeCount × Fin nodeCount))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom) :
    ∀ root,
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) ∨
      ∃ leaf, SearchDescends
          (runtimeNextBlockedFacts ontology
            (productionBlockedFacts parent ancestors forbidden)) root leaf ∧
        (((stateOfGuardedFacts leaf).productionUnwitnessedSources = [] ∧
            (FiniteSatCertificate.ofState ontology
              (stateOfGuardedFacts leaf)).checkSat = true) ∨
          ((stateOfGuardedFacts leaf).productionUnwitnessedSources ≠ [] ∧
            (stateOfGuardedFacts leaf).BlockedRuntimeTerminal ontology
              ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
                (ancestors leaf) forbidden)) ∨
          (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
            ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
              (ancestors leaf) forbidden)) := by
  intro root
  rcases finite_productionBlocked_terminal_or_frontier ontology parent ancestors
      forbidden hheads root with hrefutes | ⟨leaf, hdescends, hleaf⟩
  · exact Or.inl hrefutes
  · right
    refine ⟨leaf, hdescends, ?_⟩
    rcases hleaf with hterminal | hfrontier
    · by_cases hempty :
        (stateOfGuardedFacts leaf).productionUnwitnessedSources = []
      · exact Or.inl ⟨hempty,
          FiniteSatCertificate.checkSat_of_empty_production_terminal ontology
            (stateOfGuardedFacts leaf) (parent leaf) (ancestors leaf) forbidden
            hguarded hterminal hempty⟩
      · exact Or.inr (Or.inl ⟨hempty, hterminal⟩)
    · exact Or.inr (Or.inr hfrontier)

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

theorem State.productionFoldOptions_filtered
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (parent : Node → Option Node)
    (ancestors : Node → List Node)
    (forbidden : Finset (Node × Node)) :
    ∀ source blockers,
      (source, blockers) ∈ foldOptionsUsing
        (state.productionFold parent ancestors forbidden)
        (Classical.decRel
          (state.productionFold parent ancestors forbidden))
        state.productionUnwitnessedSources →
      ∀ blocker ∈ blockers, (source, blocker) ∉ forbidden := by
  classical
  intro source blockers hoption blocker hblocker
  simp only [foldOptionsUsing, foldOptions] at hoption
  rcases List.mem_map.mp hoption with ⟨candidate, _, heq⟩
  cases heq
  have hfold :
      state.productionFold parent ancestors forbidden source blocker := by
    simpa [foldBlockers] using hblocker
  exact state.productionFold_not_forbidden parent ancestors forbidden hfold

/-- A concrete production terminal with at least one unwitnessed source always
exposes a fresh pair for the exact outer forbidden-pair expansion. -/
theorem State.productionFoldOptionPairs_has_fresh
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
    (hne : state.productionUnwitnessedSources ≠ []) :
    ∃ pair ∈ foldOptionPairs (foldOptionsUsing
        (state.productionFold parent ancestors forbidden)
        (Classical.decRel
          (state.productionFold parent ancestors forbidden))
        state.productionUnwitnessedSources),
      pair ∉ forbidden := by
  classical
  apply foldOptionPairs_has_fresh_of_filtered
  · simpa [foldOptionsUsing, foldOptions] using hne
  · intro option hoption
    exact foldOptions_option_nonempty
      (state.productionBlocked parent ancestors forbidden)
      (state.productionFold parent ancestors forbidden)
      (state.productionBlocked_foldTotal parent ancestors forbidden)
      state.productionUnwitnessedSources
      (state.productionTerminal_sources_blocked ontology parent ancestors forbidden
        hterminal) option (by simpa [foldOptionsUsing] using hoption)
  · exact state.productionFoldOptions_filtered parent ancestors forbidden

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

/-- Construct both finite learning layers from the concrete terminal rebuilt
for each outer forbidden-pair set. Checked fold candidates can only finish;
exact Cartesian exhaustion either returns the supplied fold-free result or
expands by precisely the current production blocker pairs. -/
noncomputable def CartesianFoldExpansionRuntime.ofProductionTerminals
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : Finset (Node × Node) → State Node Concept Role)
    (decision : ∀ forbidden, DecidableState (state forbidden))
    (parent : Finset (Node × Node) → Node → Option Node)
    (ancestors : Finset (Node × Node) → Node → List Node)
    (terminal : ∀ forbidden,
      (state forbidden).BlockedRuntimeTerminal ontology
        ((state forbidden).productionBlocked (parent forbidden)
          (ancestors forbidden) forbidden))
    (candidate : ∀ _forbidden : Finset (Node × Node),
      Finset (FoldAssignment Node) → FoldAssignment Node → Option Result)
    (foldFree : ∀ forbidden,
      (state forbidden).productionUnwitnessedSources = [] → Result) :
    CartesianFoldExpansionRuntime Node Result := by
  classical
  let options (forbidden : Finset (Node × Node)) :=
    foldOptionsUsing
      ((state forbidden).productionFold (parent forbidden)
        (ancestors forbidden) forbidden)
      (Classical.decRel
        ((state forbidden).productionFold (parent forbidden)
          (ancestors forbidden) forbidden))
      (state forbidden).productionUnwitnessedSources
  let exhaustedOutcome (forbidden : Finset (Node × Node)) :=
    fun (_rejected : Finset (FoldAssignment Node))
        (_exhausted : ∀ assignment ∈ enumerateFoldAssignments
          (options forbidden), assignment ∈ _rejected) =>
      if hempty : (state forbidden).productionUnwitnessedSources = [] then
        GuardedFoldExpansionOutcome.done (foldFree forbidden hempty)
      else
        GuardedFoldExpansionOutcome.expand
          (foldOptionPairs (options forbidden))
          ((state forbidden).productionFoldOptionPairs_has_fresh ontology
            (parent forbidden) (ancestors forbidden) forbidden
            (terminal forbidden) hempty)
  let inner (forbidden : Finset (Node × Node)) :=
    letI := decision forbidden
    CartesianFoldAssignmentRuntime.ofProductionTerminal
      (state forbidden) ontology (parent forbidden)
      (ancestors forbidden) forbidden (terminal forbidden)
      (fun rejected assignment =>
        checkedFoldCandidate (candidate forbidden) forbidden rejected assignment)
      (exhaustedOutcome forbidden)
  exact {
    inner := inner
    checkConclusive := by
      intro forbidden rejected assignment outcome hcheck
      exact checkedFoldCandidate_conclusive (candidate forbidden) forbidden
        rejected assignment outcome hcheck
    expansionExact := by
      intro forbidden rejected exhausted pairs fresh hexpand
      dsimp [inner, CartesianFoldAssignmentRuntime.ofProductionTerminal,
        CartesianFoldAssignmentRuntime.ofFoldTable] at hexpand ⊢
      dsimp [exhaustedOutcome] at hexpand
      split at hexpand
      · simp at hexpand
      · exact (GuardedFoldExpansionOutcome.expand.inj hexpand).symm }

/-! ## Settled production search

The production search can close a branch or expose a node frontier before it
reaches a blocked open leaf.  Such an outcome is already conclusive for the
fixed outer forbidden-pair set and must not be forced through a fabricated
blocking table.  The package below records only the genuinely blocked case.
-/

/-- Re-index a blocked leaf from the empty forbidden set to the concrete outer
set at which it was produced.  Keeping that set in the package prevents a
terminal from being reused at a different learning state. -/
structure ProductionBlockedLeafAt
    (Node Concept Role Variable : Type)
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (forbidden : Finset (Node × Node)) where
  state : State Node Concept Role
  decision : DecidableState state
  parent : Node → Option Node
  ancestors : Node → List Node
  terminal : state.BlockedRuntimeTerminal ontology
    (state.productionBlocked parent ancestors forbidden)

noncomputable def ProductionBlockedLeafAt.unwitnessedSources
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (leaf : ProductionBlockedLeafAt Node Concept Role Variable ontology
      forbidden) : List Node := by
  letI := leaf.decision
  exact leaf.state.productionUnwitnessedSources

private def settledEarlyInner
    [DecidableEq Node]
    (forbidden : Finset (Node × Node)) (result : Result) :
    CartesianFoldAssignmentRuntime Node
      (GuardedFoldExpansionOutcome Node Result forbidden) where
  options := fun _ => []
  optionNonempty := by simp
  check := fun _ _ => .inl (.done result)
  onExhausted := fun _ _ => .done result

private noncomputable def settledBlockedInner
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (forbidden : Finset (Node × Node))
    (leaf : ProductionBlockedLeafAt Node Concept Role Variable ontology
      forbidden)
    (candidate : Finset (FoldAssignment Node) → FoldAssignment Node →
      Option Result)
    (foldFree : leaf.unwitnessedSources = [] → Result) :
    CartesianFoldAssignmentRuntime Node
      (GuardedFoldExpansionOutcome Node Result forbidden) := by
  classical
  letI := leaf.decision
  let options := foldOptionsUsing
    (leaf.state.productionFold leaf.parent leaf.ancestors forbidden)
    (Classical.decRel
      (leaf.state.productionFold leaf.parent leaf.ancestors forbidden))
    leaf.state.productionUnwitnessedSources
  let exhaustedOutcome := fun
      (_rejected : Finset (FoldAssignment Node))
      (_exhausted : ∀ assignment ∈ enumerateFoldAssignments options,
        assignment ∈ _rejected) =>
    if hempty : leaf.state.productionUnwitnessedSources = [] then
      GuardedFoldExpansionOutcome.done (foldFree (by
        simpa [ProductionBlockedLeafAt.unwitnessedSources] using hempty))
    else
      GuardedFoldExpansionOutcome.expand
        (foldOptionPairs options)
        (leaf.state.productionFoldOptionPairs_has_fresh ontology
          leaf.parent leaf.ancestors forbidden leaf.terminal hempty)
  exact CartesianFoldAssignmentRuntime.ofProductionTerminal
    leaf.state ontology leaf.parent leaf.ancestors forbidden leaf.terminal
    (fun rejected assignment =>
      checkedFoldCandidate candidate forbidden rejected assignment)
    exhaustedOutcome

private theorem settledEarlyInner_no_expand
    [DecidableEq Node]
    (forbidden : Finset (Node × Node)) (result : Result)
    (rejected : Finset (FoldAssignment Node))
    (exhausted : ∀ assignment ∈ enumerateFoldAssignments
      ((settledEarlyInner forbidden result).options rejected),
      assignment ∈ rejected)
    (pairs : Finset (Node × Node))
    (fresh : ∃ pair ∈ pairs, pair ∉ forbidden)
    (hexpand : (settledEarlyInner forbidden result).onExhausted rejected
      exhausted = GuardedFoldExpansionOutcome.expand pairs fresh) : False := by
  simp [settledEarlyInner] at hexpand

private theorem settledBlockedInner_expansionExact
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (forbidden : Finset (Node × Node))
    (leaf : ProductionBlockedLeafAt Node Concept Role Variable ontology
      forbidden)
    (candidate : Finset (FoldAssignment Node) → FoldAssignment Node →
      Option Result)
    (foldFree : leaf.unwitnessedSources = [] → Result)
    (rejected : Finset (FoldAssignment Node))
    (exhausted : ∀ assignment ∈ enumerateFoldAssignments
      ((settledBlockedInner ontology forbidden leaf candidate foldFree).options
        rejected), assignment ∈ rejected)
    (pairs : Finset (Node × Node))
    (fresh : ∃ pair ∈ pairs, pair ∉ forbidden)
    (hexpand : (settledBlockedInner ontology forbidden leaf candidate foldFree).onExhausted
        rejected exhausted =
      GuardedFoldExpansionOutcome.expand pairs fresh) :
    pairs = foldOptionPairs
      ((settledBlockedInner ontology forbidden leaf candidate foldFree).options
        rejected) := by
  classical
  letI := leaf.decision
  dsimp [settledBlockedInner,
    CartesianFoldAssignmentRuntime.ofProductionTerminal,
    CartesianFoldAssignmentRuntime.ofFoldTable] at hexpand ⊢
  split at hexpand
  · simp at hexpand
  · exact (GuardedFoldExpansionOutcome.expand.inj hexpand).symm

/-- Compute the outer settlement directly from the exhaustive finite
blocker-aware search.  The caller translates a semantic refutation or a
checked node frontier into the fixed-budget result type; a blocked-open leaf is
packaged with its exact state and blocking provenance for fold learning. -/
noncomputable def finiteProductionSearchSettlement
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → List (Fin nodeCount))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (root : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)))
    (closed : ∀ forbidden : Finset (Fin nodeCount × Fin nodeCount),
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) → Result)
    (frontier : ∀
      (forbidden : Finset (Fin nodeCount × Fin nodeCount))
      (leaf : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
        (Fin roleCount))),
      SearchDescends
        (runtimeNextBlockedFacts ontology
          (productionBlockedFacts parent ancestors forbidden)) root leaf →
      (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
        ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
          (ancestors leaf) forbidden) → Result) :
    ∀ forbidden : Finset (Fin nodeCount × Fin nodeCount),
      Result ⊕ ProductionBlockedLeafAt (Fin nodeCount) (Fin conceptCount)
        (Fin roleCount) (Fin variableCount) ontology forbidden := by
  classical
  intro forbidden
  exact Classical.choice (show Nonempty
      (Result ⊕ ProductionBlockedLeafAt (Fin nodeCount) (Fin conceptCount)
        (Fin roleCount) (Fin variableCount) ontology forbidden) from by
    rcases finite_productionBlocked_terminal_or_frontier ontology parent ancestors
        forbidden hheads root with hrefutes | ⟨leaf, hdescends, hsettled⟩
    · exact ⟨.inl (closed forbidden hrefutes)⟩
    · rcases hsettled with hterminal | hfrontier
      · exact ⟨.inr {
          state := stateOfGuardedFacts leaf
          decision := inferInstance
          parent := parent leaf
          ancestors := ancestors leaf
          terminal := hterminal }⟩
      · exact ⟨.inl (frontier forbidden leaf hdescends hfrontier)⟩)

/-- Construct the complete two-level learning runtime from a concrete search
settlement at every outer forbidden-pair set.  A refutation or checked frontier
is returned by the `done` arm immediately.  Only an actual blocked terminal is
enumerated for simultaneous fold assignments. -/
noncomputable def CartesianFoldExpansionRuntime.ofSettledProductionSearch
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (settle : ∀ forbidden : Finset (Node × Node),
      Result ⊕ ProductionBlockedLeafAt Node Concept Role Variable ontology
        forbidden)
    (candidate : ∀ _forbidden : Finset (Node × Node),
      Finset (FoldAssignment Node) → FoldAssignment Node → Option Result)
    (foldFree : ∀ forbidden
      (leaf : ProductionBlockedLeafAt Node Concept Role Variable ontology
        forbidden), leaf.unwitnessedSources = [] → Result) :
    CartesianFoldExpansionRuntime Node Result := by
  classical
  let inner (forbidden : Finset (Node × Node)) :=
    match settle forbidden with
    | .inl result => settledEarlyInner forbidden result
    | .inr leaf =>
        settledBlockedInner ontology forbidden leaf (candidate forbidden)
          (foldFree forbidden leaf)
  exact {
    inner := inner
    checkConclusive := by
      intro forbidden rejected assignment outcome hcheck
      cases hsettle : settle forbidden with
      | inl result =>
          have heq : GuardedFoldExpansionOutcome.done result = outcome := by
            simpa [inner, hsettle, settledEarlyInner] using hcheck
          exact ⟨result, heq.symm⟩
      | inr leaf =>
          have hcheck' : checkedFoldCandidate (candidate forbidden) forbidden
              rejected assignment = .inl outcome := by
            simpa [inner, hsettle, settledBlockedInner] using hcheck
          exact checkedFoldCandidate_conclusive (candidate forbidden) forbidden
            rejected assignment outcome hcheck'
    expansionExact := by
      intro forbidden rejected exhausted pairs fresh hexpand
      cases hsettle : settle forbidden with
      | inl result =>
          exact False.elim (settledEarlyInner_no_expand forbidden result
            rejected (by simpa [inner, hsettle] using exhausted) pairs fresh
            (by simpa [inner, hsettle] using hexpand))
      | inr leaf =>
          have hexact := settledBlockedInner_expansionExact ontology forbidden leaf
            (candidate forbidden) (foldFree forbidden leaf) rejected
            (by simpa [inner, hsettle] using exhausted) pairs fresh
            (by simpa [inner, hsettle] using hexpand)
          simpa [inner, hsettle] using hexact }

/-- End-to-end fixed-budget constructor from exhaustive finite search through
both finite blocker-learning layers.  No caller-supplied settlement or
universal blocked-terminal family remains. -/
noncomputable def CartesianFoldExpansionRuntime.ofFiniteProductionSearch
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → List (Fin nodeCount))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (root : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)))
    (closed : ∀ forbidden : Finset (Fin nodeCount × Fin nodeCount),
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) → Result)
    (frontier : ∀
      (forbidden : Finset (Fin nodeCount × Fin nodeCount))
      (leaf : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
        (Fin roleCount))),
      SearchDescends
        (runtimeNextBlockedFacts ontology
          (productionBlockedFacts parent ancestors forbidden)) root leaf →
      (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
        ((stateOfGuardedFacts leaf).productionBlocked (parent leaf)
          (ancestors leaf) forbidden) → Result)
    (candidate : ∀ _forbidden : Finset (Fin nodeCount × Fin nodeCount),
      Finset (FoldAssignment (Fin nodeCount)) → FoldAssignment (Fin nodeCount) →
        Option Result)
    (foldFree : ∀ forbidden
      (leaf : ProductionBlockedLeafAt (Fin nodeCount) (Fin conceptCount)
        (Fin roleCount) (Fin variableCount) ontology forbidden),
      leaf.unwitnessedSources = [] → Result) :
    CartesianFoldExpansionRuntime (Fin nodeCount) Result :=
  CartesianFoldExpansionRuntime.ofSettledProductionSearch ontology
    (finiteProductionSearchSettlement ontology parent ancestors hheads root
      closed frontier) candidate foldFree

#print axioms State.productionBlocked_eq_true_iff
#print axioms FiniteProductionBlockingTable.checkOptions_eq_true_iff
#print axioms FiniteProductionBlockingTable.checked_option_exact
#print axioms FiniteProductionBlockingTable.checked_pairs_exact
#print axioms FiniteProductionBlockingTable.parentEarlierB_eq_true_iff
#print axioms FiniteProductionBlockingTable.check_eq_true_iff
#print axioms FiniteProductionBlockingTable.check_sound
#print axioms finite_productionBlocked_terminal_or_frontier
#print axioms FiniteSatCertificate.ofState_state
#print axioms State.productionBlocked_foldTotal
#print axioms State.productionFold_not_forbidden
#print axioms State.mem_productionUnwitnessedSources_iff
#print axioms State.productionUnwitnessedSources_eq_nil_iff
#print axioms FiniteSatCertificate.checkSat_of_empty_production_terminal
#print axioms finite_productionBlocked_checked_leaf
#print axioms State.productionTerminal_sources_blocked
#print axioms State.productionTerminal_foldTable
#print axioms State.productionFoldOptions_filtered
#print axioms State.productionFoldOptionPairs_has_fresh
#print axioms CartesianFoldExpansionRuntime.ofProductionTerminals
#print axioms CartesianFoldExpansionRuntime.ofSettledProductionSearch
#print axioms finiteProductionSearchSettlement
#print axioms CartesianFoldExpansionRuntime.ofFiniteProductionSearch

end ContextCalculus.Hypertableau
