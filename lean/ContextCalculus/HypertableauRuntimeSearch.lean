import ContextCalculus.HypertableauBlockedSearch

/-!
# Executable hypertableau runtime selection

This module connects the clause-first finite enumeration used by the runtime
to `FirstObstructionStep`.  The selector is deliberately small and explicit:
it scans ontology clauses in input order and all assignments in the finite
node universe, returning the first undischarged grounding.
-/

namespace ContextCalculus.Hypertableau

/-- A proof-friendly executable first-match scan. -/
def firstMatch (p : α → Bool) : List α → Option α
  | [] => none
  | value :: rest => if p value then some value else firstMatch p rest

theorem firstMatch_eq_some_mem
    {p : α → Bool} {values : List α} {value : α}
    (h : firstMatch p values = some value) :
    value ∈ values ∧ p value = true := by
  induction values with
  | nil => simp [firstMatch] at h
  | cons head tail ih =>
      simp only [firstMatch] at h
      split at h <;> rename_i hp
      · simp_all
      · obtain ⟨hmem, hvalue⟩ := ih h
        exact ⟨by simp [hmem], hvalue⟩

theorem firstMatch_eq_none_iff
    {p : α → Bool} {values : List α} :
    firstMatch p values = none ↔ ∀ value ∈ values, p value = false := by
  induction values with
  | nil => simp [firstMatch]
  | cons head tail ih =>
      simp only [firstMatch]
      split <;> rename_i hp
      · simp_all
      · simp_all

abbrev Grounding (Variable Node Concept Role : Type) :=
  Clause Variable Concept Role × (Variable → Node)

/-- Runtime order: ontology order outside, finite assignment order inside. -/
noncomputable def allGroundings
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role)) :
    List (Grounding Variable Node Concept Role) := by
  classical
  exact ontology.flatMap fun clause =>
    (Finset.univ.toList : List (Variable → Node)).map fun assignment =>
      (clause, assignment)

theorem mem_allGroundings
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    {ontology : List (Clause Variable Concept Role)}
    {clause : Clause Variable Concept Role} {assignment : Variable → Node} :
    (clause, assignment) ∈ allGroundings ontology ↔ clause ∈ ontology := by
  classical
  simp [allGroundings]

class DecidableState (state : State Node Concept Role) where
  label : ∀ node literal, Decidable (state.label node literal)
  edge : ∀ role source target, Decidable (state.edge role source target)
  obligation : ∀ role filler node, Decidable (state.obligation role filler node)

abbrev ClashCandidate (Node Concept : Type) := Node × Concept

noncomputable def allClashCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept] :
    List (ClashCandidate Node Concept) := by
  classical
  exact (Finset.univ.toList : List Node).flatMap fun node =>
    (Finset.univ.toList : List Concept).map fun concept => (node, concept)

theorem mem_allClashCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (candidate : ClashCandidate Node Concept) :
    candidate ∈ allClashCandidates := by
  classical
  rcases candidate with ⟨node, concept⟩
  simp [allClashCandidates]

def clashCandidateBool
    (state : State Node Concept Role) [DecidableState state]
    (candidate : ClashCandidate Node Concept) : Bool :=
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  decide (state.label candidate.1 (.pos candidate.2)) &&
    decide (state.label candidate.1 (.negated candidate.2))

theorem clashCandidateBool_eq_true_iff
    (state : State Node Concept Role) [DecidableState state]
    (candidate : ClashCandidate Node Concept) :
    clashCandidateBool state candidate = true ↔
      state.label candidate.1 (.pos candidate.2) ∧
      state.label candidate.1 (.negated candidate.2) := by
  simp [clashCandidateBool]

noncomputable def selectClash
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : State Node Concept Role) [DecidableState state] :
    Option (ClashCandidate Node Concept) :=
  firstMatch (clashCandidateBool state) allClashCandidates

theorem selectClash_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : State Node Concept Role) [DecidableState state] :
    selectClash state = none ↔ ¬state.HasClash := by
  classical
  rw [selectClash, firstMatch_eq_none_iff]
  constructor
  · intro hscan hclash
    rcases hclash with ⟨node, concept, hpositive, hnegative⟩
    have hfalse := hscan (node, concept)
      (mem_allClashCandidates (node, concept))
    rw [(clashCandidateBool_eq_true_iff state (node, concept)).mpr
      ⟨hpositive, hnegative⟩] at hfalse
    contradiction
  · intro hnone candidate hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hlabels := (clashCandidateBool_eq_true_iff state candidate).mp htrue
    exact hnone ⟨candidate.1, candidate.2, hlabels.1, hlabels.2⟩

theorem selectClash_refutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    {candidate : ClashCandidate Node Concept}
    (hselect : selectClash state = some candidate) :
    Refutes Node ontology state := by
  classical
  have hfound := firstMatch_eq_some_mem (by simpa [selectClash] using hselect)
  have hlabels := (clashCandidateBool_eq_true_iff state candidate).mp hfound.2
  exact .clash state ⟨candidate.1, candidate.2, hlabels.1, hlabels.2⟩

def holdsAtomBool
    (state : State Node Concept Role)
    [DecidableEq Node]
    [DecidableState state]
    (assignment : Variable → Node) : Atom Variable Concept Role → Bool :=
  fun atom =>
    letI : ∀ node literal, Decidable (state.label node literal) :=
      DecidableState.label (state := state)
    letI : ∀ role source target, Decidable (state.edge role source target) :=
      DecidableState.edge (state := state)
    letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
      DecidableState.obligation (state := state)
    match atom with
    | .concept literal node => decide (state.label (assignment node) literal)
    | .role role source target => decide (state.edge role (assignment source) (assignment target))
    | .exists_ role filler node => decide (state.obligation role filler (assignment node))
    | .eq left right => decide (assignment left = assignment right)

@[simp] theorem holdsAtomBool_eq_true_iff
    (state : State Node Concept Role)
    [DecidableEq Node] [DecidableState state]
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    holdsAtomBool state assignment atom = true ↔ state.holdsAtom assignment atom := by
  cases atom <;> simp [holdsAtomBool, State.holdsAtom]

@[simp] theorem holdsAtomBool_eq_false_iff
    (state : State Node Concept Role)
    [DecidableEq Node] [DecidableState state]
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    holdsAtomBool state assignment atom = false ↔ ¬state.holdsAtom assignment atom := by
  rw [Bool.eq_false_iff]
  simp

def groundingUndischarged
    (state : State Node Concept Role)
    [DecidableEq Node]
    [DecidableState state]
    (grounding : Grounding Variable Node Concept Role) : Bool :=
  grounding.1.body.all (holdsAtomBool state grounding.2) &&
  grounding.1.head.all fun atom => !(holdsAtomBool state grounding.2 atom)

theorem groundingUndischarged_eq_true_iff
    {state : State Node Concept Role}
    [DecidableEq Node]
    [DecidableState state]
    {grounding : Grounding Variable Node Concept Role} :
    groundingUndischarged state grounding = true ↔
      (∀ atom ∈ grounding.1.body, state.holdsAtom grounding.2 atom) ∧
      ∀ atom ∈ grounding.1.head, ¬state.holdsAtom grounding.2 atom := by
  simp [groundingUndischarged, List.all_eq_true]

noncomputable def selectClauseGrounding
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role)
    [DecidableState state] :
    Option (Grounding Variable Node Concept Role) :=
  firstMatch (groundingUndischarged state) (allGroundings ontology)

/-- The executable finite scan misses no undischarged clause grounding. -/
theorem selectClauseGrounding_eq_none_iff
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role)
    [DecidableState state] :
    selectClauseGrounding ontology state = none ↔
      ¬state.HasUndischarged ontology := by
  classical
  rw [selectClauseGrounding, firstMatch_eq_none_iff]
  constructor
  · intro hscan hundischarged
    rcases hundischarged with ⟨clause, hclause, assignment, hbody, habsent⟩
    have hfalse := hscan (clause, assignment)
      (mem_allGroundings.mpr hclause)
    rw [groundingUndischarged_eq_true_iff.mpr ⟨hbody, habsent⟩] at hfalse
    contradiction
  · intro hnone grounding hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    rcases grounding with ⟨clause, assignment⟩
    have hclause := mem_allGroundings.mp hmem
    have hproperties := groundingUndischarged_eq_true_iff.mp htrue
    exact hnone ⟨clause, hclause, assignment,
      hproperties.1, hproperties.2⟩

/-- A selected equality-free grounding is exactly the runtime branch shape. -/
theorem selectClauseGrounding_firstObstructionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role)
    [DecidableState state]
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    {grounding : Grounding Variable Node Concept Role}
    (hselect : selectClauseGrounding ontology state = some grounding) :
    FirstObstructionStep ontology state
      (grounding.1.head.map (state.assertAtom grounding.2)) := by
  classical
  have hfound := firstMatch_eq_some_mem (by simpa [selectClauseGrounding] using hselect)
  rcases grounding with ⟨clause, assignment⟩
  have hclause : clause ∈ ontology := mem_allGroundings.mp hfound.1
  have hproperties := groundingUndischarged_eq_true_iff.mp hfound.2
  exact .branch clause hclause assignment hproperties.1 hproperties.2
    (hheads clause hclause)

/-- An undischarged empty-head clause closes immediately. Although its
successor list is empty, it is a zero-child refutation rule rather than an open
search terminal. -/
theorem selectClauseGrounding_emptyHead_refutes
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    {grounding : Grounding Variable Node Concept Role}
    (hselect : selectClauseGrounding ontology state = some grounding)
    (hempty : grounding.1.head = []) : Refutes Node ontology state := by
  have hstep := selectClauseGrounding_firstObstructionStep ontology state
    hheads hselect
  apply hstep.exhaustiveStep.refutes_of_children
  intro child hchild
  simp [hempty] at hchild

abbrev WitnessCandidate (Node Concept Role : Type) := Role × Lit Concept × Node

noncomputable def allWitnessCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role] :
    List (WitnessCandidate Node Concept Role) := by
  classical
  exact (Finset.univ.toList : List Role).flatMap fun role =>
    (Finset.univ.toList : List Concept).flatMap fun concept =>
    [false, true].flatMap fun neg =>
    (Finset.univ.toList : List Node).map fun source =>
      (role, ⟨concept, neg⟩, source)

theorem mem_allWitnessCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (candidate : WitnessCandidate Node Concept Role) :
    candidate ∈ allWitnessCandidates := by
  classical
  rcases candidate with ⟨role, ⟨concept, neg⟩, source⟩
  cases neg <;> simp [allWitnessCandidates]

noncomputable def witnessCandidateBool
    (state : State Node Concept Role)
    [Fintype Node] [DecidableEq Node] [DecidableState state]
    (candidate : WitnessCandidate Node Concept Role) : Bool :=
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  decide (state.obligation candidate.1 candidate.2.1 candidate.2.2) &&
    (Finset.univ.toList : List Node).all fun witness =>
      decide (¬(state.edge candidate.1 candidate.2.2 witness ∧
        state.label witness candidate.2.1))

theorem witnessCandidateBool_eq_true_iff
    (state : State Node Concept Role)
    [Fintype Node] [DecidableEq Node] [DecidableState state]
    (candidate : WitnessCandidate Node Concept Role) :
    witnessCandidateBool state candidate = true ↔
      state.obligation candidate.1 candidate.2.1 candidate.2.2 ∧
      ∀ witness, ¬(state.edge candidate.1 candidate.2.2 witness ∧
        state.label witness candidate.2.1) := by
  classical
  letI : ∀ node literal, Decidable (state.label node literal) :=
    DecidableState.label (state := state)
  letI : ∀ role source target, Decidable (state.edge role source target) :=
    DecidableState.edge (state := state)
  letI : ∀ role filler node, Decidable (state.obligation role filler node) :=
    DecidableState.obligation (state := state)
  simp only [witnessCandidateBool, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Finset.mem_toList, Finset.mem_univ, true_implies]

noncomputable def selectUnwitnessed
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state] :
    Option (WitnessCandidate Node Concept Role) :=
  firstMatch (witnessCandidateBool state) allWitnessCandidates

theorem selectUnwitnessed_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state] :
    selectUnwitnessed state = none ↔ ¬state.HasUnwitnessed := by
  classical
  rw [selectUnwitnessed, firstMatch_eq_none_iff]
  constructor
  · intro hscan hunwitnessed
    rcases hunwitnessed with ⟨source, role, filler, hobligation, hnowitness⟩
    have hfalse := hscan (role, filler, source)
      (mem_allWitnessCandidates (role, filler, source))
    rw [(witnessCandidateBool_eq_true_iff state (role, filler, source)).mpr
      ⟨hobligation, hnowitness⟩] at hfalse
    contradiction
  · intro hnone candidate hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hproperties := (witnessCandidateBool_eq_true_iff state candidate).mp htrue
    exact hnone ⟨candidate.2.2, candidate.1, candidate.2.1,
      hproperties.1, hproperties.2⟩

noncomputable def unblockedWitnessCandidateBool
    (state : State Node Concept Role)
    [Fintype Node] [DecidableEq Node] [DecidableState state]
    (blocked : Node → Bool)
    (candidate : WitnessCandidate Node Concept Role) : Bool :=
  witnessCandidateBool state candidate && !blocked candidate.2.2

theorem unblockedWitnessCandidateBool_eq_true_iff
    (state : State Node Concept Role)
    [Fintype Node] [DecidableEq Node] [DecidableState state]
    (blocked : Node → Bool)
    (candidate : WitnessCandidate Node Concept Role) :
    unblockedWitnessCandidateBool state blocked candidate = true ↔
      state.obligation candidate.1 candidate.2.1 candidate.2.2 ∧
      (∀ witness, ¬(state.edge candidate.1 candidate.2.2 witness ∧
        state.label witness candidate.2.1)) ∧ blocked candidate.2.2 = false := by
  simp [unblockedWitnessCandidateBool,
    witnessCandidateBool_eq_true_iff, and_assoc]

noncomputable def selectUnblockedUnwitnessed
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool) : Option (WitnessCandidate Node Concept Role) :=
  firstMatch (unblockedWitnessCandidateBool state blocked) allWitnessCandidates

/-- Exhausting the blocker-aware scan means every still-unwitnessed source is
reported blocked. This is the exact logical contract of Rust's
`pairwise_blocked_by_ancestor` filter; the blocker/fold checker separately
validates whether those reports justify a model. -/
theorem selectUnblockedUnwitnessed_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool) :
    selectUnblockedUnwitnessed state blocked = none ↔
      ∀ source role filler, state.obligation role filler source →
        (∀ witness, ¬(state.edge role source witness ∧
          state.label witness filler)) → blocked source = true := by
  classical
  rw [selectUnblockedUnwitnessed, firstMatch_eq_none_iff]
  constructor
  · intro hscan source role filler hobligation hnowitness
    have hfalse := hscan (role, filler, source)
      (mem_allWitnessCandidates (role, filler, source))
    by_contra hblocked
    have hblockedFalse : blocked source = false := by
      cases hvalue : blocked source <;> simp_all
    have htrue : unblockedWitnessCandidateBool state blocked
        (role, filler, source) = true :=
      (unblockedWitnessCandidateBool_eq_true_iff state blocked
        (role, filler, source)).mpr ⟨hobligation, hnowitness, hblockedFalse⟩
    rw [htrue] at hfalse
    contradiction
  · intro hall candidate hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hproperties := (unblockedWitnessCandidateBool_eq_true_iff
      state blocked candidate).mp htrue
    have hblocked := hall candidate.2.2 candidate.1 candidate.2.1
      hproperties.1 hproperties.2.1
    rw [hproperties.2.2] at hblocked
    contradiction

noncomputable def freshNodeBool
    (state : State Node Concept Role)
    [Fintype Node] [DecidableEq Node]
    (target : Node) : Bool := by
  classical
  exact decide (target ∉ state.activeNodes)

@[simp] theorem freshNodeBool_eq_true_iff
    (state : State Node Concept Role)
    [Fintype Node] [DecidableEq Node]
    (target : Node) : freshNodeBool state target = true ↔ state.Fresh target := by
  classical
  simp [freshNodeBool, state.fresh_iff_not_mem_activeNodes]

noncomputable def selectFreshNode
    [Fintype Node] [DecidableEq Node]
    (state : State Node Concept Role) : Option Node :=
  firstMatch (freshNodeBool state) Finset.univ.toList

theorem selectFreshNode_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    (state : State Node Concept Role) :
    selectFreshNode state = none ↔ ¬∃ target, state.Fresh target := by
  classical
  rw [selectFreshNode, firstMatch_eq_none_iff]
  constructor
  · intro hscan hexists
    rcases hexists with ⟨target, hfresh⟩
    have hfalse := hscan target (by simp)
    rw [(freshNodeBool_eq_true_iff state target).mpr hfresh] at hfalse
    contradiction
  · intro hnone target _
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hnone ⟨target, (freshNodeBool_eq_true_iff state target).mp htrue⟩

theorem selectUnblockedUnwitnessed_firstObstructionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool)
    (hclauses : selectClauseGrounding ontology state = none)
    {candidate : WitnessCandidate Node Concept Role}
    (hwitness : selectUnblockedUnwitnessed state blocked = some candidate)
    {target : Node} (hfresh : selectFreshNode state = some target) :
    FirstObstructionStep ontology state
      [state.materializeWitness candidate.2.2 target candidate.1 candidate.2.1] := by
  classical
  have hcandidate := firstMatch_eq_some_mem
    (by simpa [selectUnblockedUnwitnessed] using hwitness)
  have htarget := firstMatch_eq_some_mem
    (by simpa [selectFreshNode] using hfresh)
  have hproperties := (unblockedWitnessCandidateBool_eq_true_iff
    state blocked candidate).mp hcandidate.2
  exact .witness ((selectClauseGrounding_eq_none_iff ontology state).mp hclauses)
    candidate.2.2 target candidate.1 candidate.2.1
    hproperties.1 hproperties.2.1
    ((freshNodeBool_eq_true_iff state target).mp htarget.2)

/-- Concrete transition enumerator with the runtime's blocker filter. The
Boolean blocker itself remains untrusted; a terminal model is accepted only
through the independent finite-fold checker. -/
noncomputable def runtimeNextBlocked
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool) : List (State Node Concept Role) :=
  match selectClauseGrounding ontology state with
  | some grounding => grounding.1.head.map (state.assertAtom grounding.2)
  | none =>
      match selectUnblockedUnwitnessed state blocked with
      | none => []
      | some candidate =>
          match selectFreshNode state with
          | none => []
          | some target =>
              [state.materializeWitness candidate.2.2 target
                candidate.1 candidate.2.1]

theorem runtimeNextBlocked_firstObstructionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hnonempty : runtimeNextBlocked ontology state blocked ≠ []) :
    FirstObstructionStep ontology state
      (runtimeNextBlocked ontology state blocked) := by
  classical
  unfold runtimeNextBlocked at hnonempty ⊢
  generalize hclause : selectClauseGrounding ontology state = selectedClause
  cases selectedClause with
  | some grounding =>
      exact selectClauseGrounding_firstObstructionStep ontology state hheads hclause
  | none =>
      generalize hwitness : selectUnblockedUnwitnessed state blocked = selectedWitness
      cases selectedWitness with
      | none =>
          exfalso
          apply hnonempty
          simp [hclause, hwitness]
      | some candidate =>
          generalize hfresh : selectFreshNode state = selectedFresh
          cases selectedFresh with
          | none =>
              exfalso
              apply hnonempty
              simp [hclause, hwitness, hfresh]
          | some target =>
              exact selectUnblockedUnwitnessed_firstObstructionStep
                ontology state blocked hclause hwitness hfresh

/-- Exact top-level ordering of the equality-free recursive runtime: a selected
clash closes immediately; only a clash-free state reaches the blocker-aware
clause/witness transition selector. -/
theorem clashFirst_runtime_control
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom) :
    Refutes Node ontology state ∨
      (¬state.HasClash ∧
        ((runtimeNextBlocked ontology state blocked ≠ [] ∧
          FirstObstructionStep ontology state
            (runtimeNextBlocked ontology state blocked)) ∨
        runtimeNextBlocked ontology state blocked = [])) := by
  classical
  generalize hclash : selectClash state = selectedClash
  cases selectedClash with
  | some candidate => exact Or.inl (selectClash_refutes ontology state hclash)
  | none =>
      right
      refine ⟨(selectClash_eq_none_iff state).mp hclash, ?_⟩
      by_cases hnext : runtimeNextBlocked ontology state blocked = []
      · exact Or.inr hnext
      · exact Or.inl ⟨hnext,
          runtimeNextBlocked_firstObstructionStep ontology state blocked
            hheads hnext⟩

/-- Exact semantic shape of a blocker-aware open terminal. Every ordinary
clause grounding is discharged, and every remaining unwitnessed obligation is
explicitly classified as blocked by the concrete Boolean selector. -/
def State.BlockedRuntimeTerminal
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (blocked : Node → Bool) : Prop :=
  ¬state.HasClash ∧ ¬state.HasUndischarged ontology ∧
    ∀ source role filler, state.obligation role filler source →
      (∀ witness, ¬(state.edge role source witness ∧ state.label witness filler)) →
      blocked source = true

/-- A blocker-aware bounded search may also stop because one unblocked
obligation remains but the finite node universe has no fresh target. -/
def State.BlockedRuntimeFrontier
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (blocked : Node → Bool) : Prop :=
  ¬state.HasClash ∧ ¬state.HasUndischarged ontology ∧
    ∃ source role filler,
      state.obligation role filler source ∧
      (∀ witness, ¬(state.edge role source witness ∧ state.label witness filler)) ∧
      blocked source = false ∧ ¬∃ target, state.Fresh target

/-- Empty blocker-aware runtime search has no hidden fourth meaning: it is a
checked refutation shape, a saturated blocked-open terminal, or explicit node
exhaustion at an unblocked existential. This is the terminal classification
used by Rust's `lean_refutation` producer. -/
theorem runtimeNextBlocked_empty_semantics
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (blocked : Node → Bool)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hempty : runtimeNextBlocked ontology state blocked = []) :
    Refutes Node ontology state ∨ state.BlockedRuntimeTerminal ontology blocked ∨
      state.BlockedRuntimeFrontier ontology blocked := by
  classical
  rcases clashFirst_runtime_control ontology state blocked hheads with
    hrefutes | ⟨hnoClash, hnext | _⟩
  · exact Or.inl hrefutes
  · exact (hnext.1 hempty).elim
  · unfold runtimeNextBlocked at hempty
    generalize hclause : selectClauseGrounding ontology state = selectedClause at hempty
    cases selectedClause with
    | some grounding =>
        have hhead : grounding.1.head = [] := by simpa using hempty
        exact Or.inl (selectClauseGrounding_emptyHead_refutes ontology state
          hheads hclause hhead)
    | none =>
        have hnoClause := (selectClauseGrounding_eq_none_iff ontology state).mp hclause
        generalize hwitness : selectUnblockedUnwitnessed state blocked = selectedWitness at hempty
        cases selectedWitness with
        | none =>
            exact Or.inr (Or.inl ⟨hnoClash, hnoClause,
              (selectUnblockedUnwitnessed_eq_none_iff state blocked).mp hwitness⟩)
        | some candidate =>
            have hfound := firstMatch_eq_some_mem
              (by simpa [selectUnblockedUnwitnessed] using hwitness)
            have hproperties := (unblockedWitnessCandidateBool_eq_true_iff
              state blocked candidate).mp hfound.2
            generalize hfresh : selectFreshNode state = selectedFresh at hempty
            cases selectedFresh with
            | none =>
                exact Or.inr (Or.inr ⟨hnoClash, hnoClause,
                  candidate.2.2, candidate.1, candidate.2.1,
                  hproperties.1, hproperties.2.1, hproperties.2.2,
                  (selectFreshNode_eq_none_iff state).mp hfresh⟩)
            | some target => simp at hempty

theorem State.BlockedRuntimeTerminal.clashFree
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (blocked : Node → Bool)
    (hterminal : state.BlockedRuntimeTerminal ontology blocked) :
    state.ClashFree := state.clashFree_of_noClash hterminal.1

theorem State.BlockedRuntimeTerminal.saturatedFor
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (blocked : Node → Bool)
    (hterminal : state.BlockedRuntimeTerminal ontology blocked) :
    state.SaturatedFor ontology :=
  state.saturatedFor_of_noUndischarged ontology hterminal.2.1

theorem State.BlockedRuntimeTerminal.unwitnessed_is_blocked
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (blocked : Node → Bool)
    (hterminal : state.BlockedRuntimeTerminal ontology blocked)
    (source : Node) (role : Role) (filler : Lit Concept)
    (hobligation : state.obligation role filler source)
    (hnowitness : ∀ witness,
      ¬(state.edge role source witness ∧ state.label witness filler)) :
    blocked source = true :=
  hterminal.2.2 source role filler hobligation hnowitness

/-! ## Blocked-open redirected witnesses -/

def State.BlockedWitnessRefines
    (state : State Node Concept Role) (blocked : Node → Bool)
    (fold : Node → Node → Prop) : Prop :=
  ∀ source role filler, state.obligation role filler source →
    blocked source = true →
    ∃ blocker target, fold source blocker ∧
      state.edge role blocker target ∧ state.label target filler

def State.BlockedRedirectRefines
    (blocked : Node → Bool) (fold : Node → Node → Prop)
    (redirect : Node → Node) : Prop :=
  (∀ source, blocked source = false → redirect source = source) ∧
  (∀ source blocker, fold source blocker → redirect source = blocker)

/-- Local node facts are invariant under a blocker redirect. Obligations must
be included alongside labels because the producer stores existential heads
outside the signed concept label. -/
def State.RedirectLocalFacts
    (state : State Node Concept Role) (redirect : Node → Node) : Prop :=
  (∀ node literal, state.label node literal ↔
    state.label (redirect node) literal) ∧
  ∀ node role filler, state.obligation role filler node ↔
    state.obligation role filler (redirect node)

/-- Every concrete fold preserves all node-local facts consulted by a local HT
residual clause. Existential obligations are explicit because Rust stores them
outside the signed concept label. -/
def State.FoldPreservesLocalFacts
    (state : State Node Concept Role) (fold : Node → Node → Prop) : Prop :=
  ∀ source blocker, fold source blocker →
    (∀ literal, state.label source literal ↔ state.label blocker literal) ∧
    ∀ role filler, state.obligation role filler source ↔
      state.obligation role filler blocker

/-- The runtime fold table is total exactly on nodes marked blocked. -/
def State.BlockedFoldTotal
    (blocked : Node → Bool) (fold : Node → Node → Prop) : Prop :=
  ∀ source, blocked source = true → ∃ blocker, fold source blocker

/-- A total local-fact-preserving fold and its concrete redirect establish the
redirect invariant used by the local regular-cover producer theorem. -/
theorem State.redirectLocalFacts_of_fold
    (state : State Node Concept Role) (blocked : Node → Bool)
    (fold : Node → Node → Prop) (redirect : Node → Node)
    (htotal : State.BlockedFoldTotal blocked fold)
    (hpreserves : state.FoldPreservesLocalFacts fold)
    (hredirect : State.BlockedRedirectRefines blocked fold redirect) :
    state.RedirectLocalFacts redirect := by
  constructor
  · intro source literal
    cases hblocked : blocked source with
    | false => simp [hredirect.1 source hblocked]
    | true =>
        obtain ⟨blocker, hfold⟩ := htotal source hblocked
        rw [hredirect.2 source blocker hfold]
        exact (hpreserves source blocker hfold).1 literal
  · intro source role filler
    cases hblocked : blocked source with
    | false => simp [hredirect.1 source hblocked]
    | true =>
        obtain ⟨blocker, hfold⟩ := htotal source hblocked
        rw [hredirect.2 source blocker hfold]
        exact (hpreserves source blocker hfold).2 role filler

/-- A blocked terminal already has every witness needed by the regular
unravelling at the redirected endpoint. Unblocked obligations retain their
ordinary witness; a blocked unwitnessed obligation uses the checked blocker's
witness. No edge copying is needed. -/
theorem State.blockedRedirectWitnessComplete
    (state : State Node Concept Role) (ontology : List (Clause Variable Concept Role))
    (blocked : Node → Bool) (fold : Node → Node → Prop)
    (redirect : Node → Node)
    (hterminal : state.BlockedRuntimeTerminal ontology blocked)
    (hrefines : state.BlockedWitnessRefines blocked fold)
    (hredirect : State.BlockedRedirectRefines blocked fold redirect) :
    state.RedirectWitnessComplete redirect := by
  intro source role filler hobligation
  by_cases hexisting : ∃ target,
      state.edge role source target ∧ state.label target filler
  · rcases hexisting with ⟨target, hedge, hlabel⟩
    cases hblocked : blocked source with
    | false =>
        rw [hredirect.1 source hblocked]
        exact ⟨target, hedge, hlabel⟩
    | true =>
        rcases hrefines source role filler hobligation hblocked with
          ⟨blocker, blockerTarget, hfold, hedgeBlocker, hlabelBlocker⟩
        rw [hredirect.2 source blocker hfold]
        exact ⟨blockerTarget, hedgeBlocker, hlabelBlocker⟩
  · have hnowitness : ∀ target,
        ¬(state.edge role source target ∧ state.label target filler) := by
      intro target hwitness
      exact hexisting ⟨target, hwitness⟩
    have hblocked := State.BlockedRuntimeTerminal.unwitnessed_is_blocked
      state ontology blocked hterminal source role filler hobligation hnowitness
    rcases hrefines source role filler hobligation hblocked with
      ⟨blocker, target, hfold, hedge, hlabel⟩
    rw [hredirect.2 source blocker hfold]
    exact ⟨target, hedge, hlabel⟩

/-- Once clause scanning is exhausted, selected obligation and fresh-node
scans construct exactly the runtime witness transition shape. -/
theorem selectUnwitnessed_firstObstructionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (hclauses : selectClauseGrounding ontology state = none)
    {candidate : WitnessCandidate Node Concept Role}
    (hwitness : selectUnwitnessed state = some candidate)
    {target : Node} (hfresh : selectFreshNode state = some target) :
    FirstObstructionStep ontology state
      [state.materializeWitness candidate.2.2 target candidate.1 candidate.2.1] := by
  classical
  have hcandidate := firstMatch_eq_some_mem
    (by simpa [selectUnwitnessed] using hwitness)
  have htarget := firstMatch_eq_some_mem
    (by simpa [selectFreshNode] using hfresh)
  have hproperties := (witnessCandidateBool_eq_true_iff state candidate).mp hcandidate.2
  exact .witness ((selectClauseGrounding_eq_none_iff ontology state).mp hclauses)
    candidate.2.2 target candidate.1 candidate.2.1
    hproperties.1 hproperties.2 ((freshNodeBool_eq_true_iff state target).mp htarget.2)

/-- Concrete clause-first transition enumerator. An empty result means either
there is no raw obstruction or an unwitnessed obligation has exhausted the
finite node universe; callers must distinguish a checked terminal from that
explicit frontier condition. -/
noncomputable def runtimeNext
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state] :
    List (State Node Concept Role) :=
  match selectClauseGrounding ontology state with
  | some grounding => grounding.1.head.map (state.assertAtom grounding.2)
  | none =>
      match selectUnwitnessed state with
      | none => []
      | some candidate =>
          match selectFreshNode state with
          | none => []
          | some target =>
              [state.materializeWitness candidate.2.2 target
                candidate.1 candidate.2.1]

/-- Every nonempty concrete runtime successor family is one exact certified
clause-first HT transition. -/
theorem runtimeNext_firstObstructionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hnonempty : runtimeNext ontology state ≠ []) :
    FirstObstructionStep ontology state (runtimeNext ontology state) := by
  classical
  unfold runtimeNext at hnonempty ⊢
  generalize hclause : selectClauseGrounding ontology state = selectedClause
  cases selectedClause with
  | some grounding =>
      exact selectClauseGrounding_firstObstructionStep ontology state hheads hclause
  | none =>
      generalize hwitness : selectUnwitnessed state = selectedWitness
      cases selectedWitness with
      | none =>
          exfalso
          apply hnonempty
          simp [hclause, hwitness]
      | some candidate =>
          generalize hfresh : selectFreshNode state = selectedFresh
          cases selectedFresh with
          | none =>
              exfalso
              apply hnonempty
              simp [hclause, hwitness, hfresh]
          | some target =>
              exact selectUnwitnessed_firstObstructionStep ontology state
                hclause hwitness hfresh

/-- Empty concrete search after both scans are exhausted is a raw semantic
terminal: no clause grounding and no existential obligation remain. -/
theorem runtimeNext_empty_terminal
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (hclause : selectClauseGrounding ontology state = none)
    (hwitness : selectUnwitnessed state = none) :
    runtimeNext ontology state = [] ∧
      ¬state.HasUndischarged ontology ∧ ¬state.HasUnwitnessed := by
  constructor
  · simp [runtimeNext, hclause, hwitness]
  · exact ⟨(selectClauseGrounding_eq_none_iff ontology state).mp hclause,
      (selectUnwitnessed_eq_none_iff state).mp hwitness⟩

/-- Empty concrete successor lists have exactly three meanings: a zero-head
refutation, a raw saturated terminal, or finite-node exhaustion while a witness
is still required. In particular, node-budget exhaustion is never classified
as a model. -/
theorem runtimeNext_empty_semantics
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) [DecidableState state]
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hempty : runtimeNext ontology state = []) :
    Refutes Node ontology state ∨
      (¬state.HasUndischarged ontology ∧ ¬state.HasUnwitnessed) ∨
      (¬state.HasUndischarged ontology ∧ state.HasUnwitnessed ∧
        ¬∃ target, state.Fresh target) := by
  classical
  unfold runtimeNext at hempty
  generalize hclause : selectClauseGrounding ontology state = selectedClause at hempty
  cases selectedClause with
  | some grounding =>
      have hhead : grounding.1.head = [] := by simpa using hempty
      exact Or.inl (selectClauseGrounding_emptyHead_refutes ontology state
        hheads hclause hhead)
  | none =>
      have hnoClause := (selectClauseGrounding_eq_none_iff ontology state).mp hclause
      generalize hwitness : selectUnwitnessed state = selectedWitness at hempty
      cases selectedWitness with
      | none =>
          exact Or.inr (Or.inl ⟨hnoClause,
            (selectUnwitnessed_eq_none_iff state).mp hwitness⟩)
      | some candidate =>
          have hunwitnessed : state.HasUnwitnessed := by
            have hfound := firstMatch_eq_some_mem
              (by simpa [selectUnwitnessed] using hwitness)
            have hproperties :=
              (witnessCandidateBool_eq_true_iff state candidate).mp hfound.2
            exact ⟨candidate.2.2, candidate.1, candidate.2.1,
              hproperties.1, hproperties.2⟩
          generalize hfresh : selectFreshNode state = selectedFresh at hempty
          cases selectedFresh with
          | none =>
              exact Or.inr (Or.inr ⟨hnoClause, hunwitnessed,
                (selectFreshNode_eq_none_iff state).mp hfresh⟩)
          | some target => simp at hempty

noncomputable instance decidableState_stateOfGuardedFacts
    [DecidableEq Node] [DecidableEq Concept] [DecidableEq Role]
    (facts : Finset (GuardedFact Node Concept Role)) :
    DecidableState (stateOfGuardedFacts facts) := by
  classical
  exact {
    label := fun _ _ => inferInstance
    edge := fun _ _ _ => inferInstance
    obligation := fun _ _ _ => inferInstance
  }

noncomputable def runtimeNextFacts
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (facts : Finset (GuardedFact Node Concept Role)) :
    List (Finset (GuardedFact Node Concept Role)) :=
  (runtimeNext ontology (stateOfGuardedFacts facts)).map State.guardedFacts

/-- Guarded-fact representation of the concrete blocker-aware successor
enumerator. The blocker is recomputed from each recursive state, matching the
production search rather than being frozen at the root. -/
noncomputable def runtimeNextBlockedFacts
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (blocked : Finset (GuardedFact Node Concept Role) → Node → Bool)
    (facts : Finset (GuardedFact Node Concept Role)) :
    List (Finset (GuardedFact Node Concept Role)) :=
  (runtimeNextBlocked ontology (stateOfGuardedFacts facts) (blocked facts)).map
    State.guardedFacts

/-- Finite exhaustive correspondence for the actual blocker-aware recursive
selector. Every root is refuted, or reaches a descended leaf classified
exactly as a blocked terminal or an explicit finite-node frontier. In
particular, this theorem does not turn a blocked terminal into a model; that
step remains the responsibility of the independently checked finite or regular
certificate. -/
theorem finite_runtimeNextBlocked_terminal_or_frontier
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (blocked : Finset (GuardedFact (Fin nodeCount) (Fin conceptCount)
      (Fin roleCount)) → Fin nodeCount → Bool)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom) :
    ∀ root,
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) ∨
      ∃ leaf, SearchDescends (runtimeNextBlockedFacts ontology blocked) root leaf ∧
        ((stateOfGuardedFacts leaf).BlockedRuntimeTerminal ontology
            (blocked leaf) ∨
          (stateOfGuardedFacts leaf).BlockedRuntimeFrontier ontology
            (blocked leaf)) := by
  apply finite_exhaustive_search_total (runtimeNextBlockedFacts ontology blocked)
    (fun facts => Refutes (Fin nodeCount) ontology (stateOfGuardedFacts facts))
    (fun facts =>
      (stateOfGuardedFacts facts).BlockedRuntimeTerminal ontology
          (blocked facts) ∨
        (stateOfGuardedFacts facts).BlockedRuntimeFrontier ontology
          (blocked facts))
  · intro parent child hchild
    have hnonempty : runtimeNextBlockedFacts ontology blocked parent ≠ [] := by
      intro hempty
      simp [hempty] at hchild
    have hruntime : runtimeNextBlocked ontology (stateOfGuardedFacts parent)
        (blocked parent) ≠ [] := by
      intro hempty
      apply hnonempty
      simp [runtimeNextBlockedFacts, hempty]
    have hstep := runtimeNextBlocked_firstObstructionStep ontology
      (stateOfGuardedFacts parent) (blocked parent) hheads hruntime
    rcases List.mem_map.mp hchild with ⟨runtimeChild, hruntimeChild, rfl⟩
    simpa using hstep.children_strictGrowth hruntimeChild
  · intro facts hempty
    have hruntimeEmpty : runtimeNextBlocked ontology (stateOfGuardedFacts facts)
        (blocked facts) = [] := by
      simpa [runtimeNextBlockedFacts] using hempty
    exact runtimeNextBlocked_empty_semantics ontology
      (stateOfGuardedFacts facts) (blocked facts) hheads hruntimeEmpty
  · intro facts hnonempty hchildren
    have hruntime : runtimeNextBlocked ontology (stateOfGuardedFacts facts)
        (blocked facts) ≠ [] := by
      intro hempty
      apply hnonempty
      simp [runtimeNextBlockedFacts, hempty]
    have hstep := runtimeNextBlocked_firstObstructionStep ontology
      (stateOfGuardedFacts facts) (blocked facts) hheads hruntime
    apply hstep.exhaustiveStep.refutes_of_children
    intro child hchild
    have hchildFacts : child.guardedFacts ∈
        runtimeNextBlockedFacts ontology blocked facts := by
      exact List.mem_map_of_mem hchild
    have hrefutes := hchildren child.guardedFacts hchildFacts
    simpa using hrefutes

/-- The finite HT decision theorem instantiated with the concrete executable
clause/witness selector. Only checked terminal production remains a runtime
premise; transition validity and strict growth are now derived in Lean. -/
theorem finite_runtimeNext_decides
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom)
    (hterminal : ∀ facts, runtimeNextFacts ontology facts = [] →
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts facts) ∨
      HasCheckedFoldModel (nodeCount := nodeCount) ontology) :
    ∀ root, Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) ∨
      HasModel ontology := by
  apply finite_first_obstruction_ht_decides ontology
    (runtimeNextFacts ontology) ?_ hterminal
  intro facts hnonempty
  have hruntime : runtimeNext ontology (stateOfGuardedFacts facts) ≠ [] := by
    intro hempty
    apply hnonempty
    simp [runtimeNextFacts, hempty]
  have hstep := runtimeNext_firstObstructionStep ontology
    (stateOfGuardedFacts facts) hheads hruntime
  have hdecode :
      ((runtimeNext ontology (stateOfGuardedFacts facts)).map State.guardedFacts).map
          stateOfGuardedFacts =
        runtimeNext ontology (stateOfGuardedFacts facts) := by
    rw [List.map_map]
    induction runtimeNext ontology (stateOfGuardedFacts facts) with
    | nil => rfl
    | cons child rest ih =>
        simp only [List.map_cons, Function.comp_apply, ih]
        rw [State.stateOfGuardedFacts_guardedFacts]
  simpa only [runtimeNextFacts, hdecode] using hstep

def RuntimeNodeFrontier
    (ontology : List (Clause Variable Concept Role))
    (state : State Node Concept Role) : Prop :=
  ¬state.HasUndischarged ontology ∧ state.HasUnwitnessed ∧
    ¬∃ target, state.Fresh target

/-- Fully discharged equality-free runtime correspondence at one finite node
budget. The concrete clause-first selector either refutes the root, reaches a
canonical model, or reaches an explicit node-exhaustion frontier. No unchecked
terminal-production premise remains, and frontier exhaustion is never
classified as satisfiable. -/
theorem finite_runtimeNext_semantic_or_frontier
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hheads : ∀ clause ∈ ontology, ∀ atom ∈ clause.head, Branchable atom) :
    ∀ root,
      Refutes (Fin nodeCount) ontology (stateOfGuardedFacts root) ∨
      ∃ leaf, SearchDescends (runtimeNextFacts ontology) root leaf ∧
        ((stateOfGuardedFacts leaf).canonical.models ontology ∨
          RuntimeNodeFrontier ontology (stateOfGuardedFacts leaf)) := by
  apply finite_exhaustive_search_total (runtimeNextFacts ontology)
    (fun facts => Refutes (Fin nodeCount) ontology (stateOfGuardedFacts facts))
    (fun facts => (stateOfGuardedFacts facts).canonical.models ontology ∨
      RuntimeNodeFrontier ontology (stateOfGuardedFacts facts))
  · intro parent child hchild
    have hnonempty : runtimeNextFacts ontology parent ≠ [] := by
      intro hempty
      simp [hempty] at hchild
    have hruntime : runtimeNext ontology (stateOfGuardedFacts parent) ≠ [] := by
      intro hempty
      apply hnonempty
      simp [runtimeNextFacts, hempty]
    have hstep := runtimeNext_firstObstructionStep ontology
      (stateOfGuardedFacts parent) hheads hruntime
    rcases List.mem_map.mp hchild with ⟨runtimeChild, hruntimeChild, rfl⟩
    simpa using hstep.children_strictGrowth hruntimeChild
  · intro facts hempty
    have hruntimeEmpty : runtimeNext ontology (stateOfGuardedFacts facts) = [] := by
      simpa [runtimeNextFacts] using hempty
    rcases runtimeNext_empty_semantics ontology (stateOfGuardedFacts facts)
        hheads hruntimeEmpty with hrefutes | hterminal | hfrontier
    · exact Or.inl hrefutes
    · by_cases hclash : (stateOfGuardedFacts facts).HasClash
      · exact Or.inl (.clash _ hclash)
      · exact Or.inr (Or.inl (exhaustive_terminal_models
          (stateOfGuardedFacts facts) ontology hguarded hclash hterminal.2 hterminal.1))
    · by_cases hclash : (stateOfGuardedFacts facts).HasClash
      · exact Or.inl (.clash _ hclash)
      · exact Or.inr (Or.inr hfrontier)
  · intro facts hnonempty hchildren
    have hruntime : runtimeNext ontology (stateOfGuardedFacts facts) ≠ [] := by
      intro hempty
      apply hnonempty
      simp [runtimeNextFacts, hempty]
    have hstep := runtimeNext_firstObstructionStep ontology
      (stateOfGuardedFacts facts) hheads hruntime
    apply hstep.exhaustiveStep.refutes_of_children
    intro child hchild
    have hchildFacts : child.guardedFacts ∈ runtimeNextFacts ontology facts := by
      exact List.mem_map_of_mem hchild
    have hrefutes := hchildren child.guardedFacts hchildFacts
    simpa using hrefutes

#print axioms selectClash_eq_none_iff
#print axioms selectClash_refutes
#print axioms selectClauseGrounding_eq_none_iff
#print axioms selectClauseGrounding_firstObstructionStep
#print axioms selectClauseGrounding_emptyHead_refutes
#print axioms selectUnwitnessed_eq_none_iff
#print axioms selectUnblockedUnwitnessed_eq_none_iff
#print axioms selectFreshNode_eq_none_iff
#print axioms selectUnwitnessed_firstObstructionStep
#print axioms selectUnblockedUnwitnessed_firstObstructionStep
#print axioms runtimeNext_firstObstructionStep
#print axioms runtimeNextBlocked_firstObstructionStep
#print axioms clashFirst_runtime_control
#print axioms runtimeNextBlocked_empty_semantics
#print axioms State.BlockedRuntimeTerminal.saturatedFor
#print axioms State.blockedRedirectWitnessComplete
#print axioms runtimeNext_empty_terminal
#print axioms runtimeNext_empty_semantics
#print axioms finite_runtimeNext_decides
#print axioms finite_runtimeNext_semantic_or_frontier
#print axioms finite_runtimeNextBlocked_terminal_or_frontier

end ContextCalculus.Hypertableau
