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

#print axioms selectClauseGrounding_eq_none_iff
#print axioms selectClauseGrounding_firstObstructionStep

end ContextCalculus.Hypertableau
