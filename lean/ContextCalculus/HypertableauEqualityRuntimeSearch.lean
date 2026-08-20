import ContextCalculus.HypertableauRuntimeSearch
import ContextCalculus.HypertableauEqualitySearch

/-!
# Executable equality-aware hypertableau runtime selection

This module mirrors the first two controls of Rust's equality-aware recursive
search.  It first scans for a clash modulo the complete node equivalence, then
scans clauses in ontology order and finite assignments in enumeration order.
-/

namespace ContextCalculus.Hypertableau

abbrev EqClashCandidate (Node Concept : Type) := Node × Node × Concept

noncomputable def allEqClashCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept] :
    List (EqClashCandidate Node Concept) := by
  classical
  exact (Finset.univ.toList : List Node).flatMap fun positiveNode =>
    (Finset.univ.toList : List Node).flatMap fun negativeNode =>
      (Finset.univ.toList : List Concept).map fun concept =>
        (positiveNode, negativeNode, concept)

theorem mem_allEqClashCandidates
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (candidate : EqClashCandidate Node Concept) :
    candidate ∈ allEqClashCandidates := by
  classical
  rcases candidate with ⟨positiveNode, negativeNode, concept⟩
  simp [allEqClashCandidates]

noncomputable def eqClashCandidateBool
    (state : EqState Node Concept Role)
    (candidate : EqClashCandidate Node Concept) : Bool := by
  classical
  exact decide (state.equiv candidate.1 candidate.2.1) &&
    decide (state.base.label candidate.1 (.pos candidate.2.2)) &&
    decide (state.base.label candidate.2.1 (.negated candidate.2.2))

theorem eqClashCandidateBool_eq_true_iff
    (state : EqState Node Concept Role)
    (candidate : EqClashCandidate Node Concept) :
    eqClashCandidateBool state candidate = true ↔
      state.equiv candidate.1 candidate.2.1 ∧
      state.base.label candidate.1 (.pos candidate.2.2) ∧
      state.base.label candidate.2.1 (.negated candidate.2.2) := by
  simp [eqClashCandidateBool, and_assoc]

noncomputable def selectEqClash
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : EqState Node Concept Role) :
    Option (EqClashCandidate Node Concept) :=
  firstMatch (eqClashCandidateBool state) allEqClashCandidates

theorem selectEqClash_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : EqState Node Concept Role) :
    selectEqClash state = none ↔ state.ClosedClashFree := by
  classical
  rw [selectEqClash, firstMatch_eq_none_iff]
  constructor
  · intro hscan positiveNode negativeNode concept hequiv hlabels
    have hfalse := hscan (positiveNode, negativeNode, concept)
      (mem_allEqClashCandidates (positiveNode, negativeNode, concept))
    rw [(eqClashCandidateBool_eq_true_iff state _).mpr
      ⟨hequiv, hlabels⟩] at hfalse
    contradiction
  · intro hfree candidate _
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hclash := (eqClashCandidateBool_eq_true_iff state candidate).mp htrue
    exact hfree candidate.1 candidate.2.1 candidate.2.2 hclash.1 hclash.2

theorem selectEqClash_refutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role)
    {candidate : EqClashCandidate Node Concept}
    (hselect : selectEqClash state = some candidate) :
    EqRefutes Node ontology state := by
  classical
  have hfound := firstMatch_eq_some_mem (by simpa [selectEqClash] using hselect)
  have hclash := (eqClashCandidateBool_eq_true_iff state candidate).mp hfound.2
  exact .clash state ⟨candidate.1, candidate.2.1, candidate.2.2,
    hclash.1, hclash.2.1, hclash.2.2⟩

noncomputable def closedHoldsAtomBool
    (state : EqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) : Bool := by
  classical
  exact decide (state.closedHoldsAtom assignment atom)

@[simp] theorem closedHoldsAtomBool_eq_true_iff
    (state : EqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    closedHoldsAtomBool state assignment atom = true ↔
      state.closedHoldsAtom assignment atom := by
  simp [closedHoldsAtomBool]

@[simp] theorem closedHoldsAtomBool_eq_false_iff
    (state : EqState Node Concept Role)
    (assignment : Variable → Node) (atom : Atom Variable Concept Role) :
    closedHoldsAtomBool state assignment atom = false ↔
      ¬state.closedHoldsAtom assignment atom := by
  rw [Bool.eq_false_iff]
  simp

noncomputable def eqGroundingUndischarged
    (state : EqState Node Concept Role)
    (grounding : Grounding Variable Node Concept Role) : Bool :=
  grounding.1.body.all (closedHoldsAtomBool state grounding.2) &&
    grounding.1.head.all fun atom => !(closedHoldsAtomBool state grounding.2 atom)

theorem eqGroundingUndischarged_eq_true_iff
    {state : EqState Node Concept Role}
    {grounding : Grounding Variable Node Concept Role} :
    eqGroundingUndischarged state grounding = true ↔
      (∀ atom ∈ grounding.1.body, state.closedHoldsAtom grounding.2 atom) ∧
      ∀ atom ∈ grounding.1.head, ¬state.closedHoldsAtom grounding.2 atom := by
  simp [eqGroundingUndischarged, List.all_eq_true]

noncomputable def selectEqClauseGrounding
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role) :
    Option (Grounding Variable Node Concept Role) :=
  firstMatch (eqGroundingUndischarged state) (allGroundings ontology)

def EqState.HasClosedUndischarged
    (state : EqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ clause ∈ ontology, ∃ assignment,
    (∀ atom ∈ clause.body, state.closedHoldsAtom assignment atom) ∧
    ∀ atom ∈ clause.head, ¬state.closedHoldsAtom assignment atom

theorem selectEqClauseGrounding_eq_none_iff
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : EqState Node Concept Role) :
    selectEqClauseGrounding ontology state = none ↔
      ¬state.HasClosedUndischarged ontology := by
  classical
  rw [selectEqClauseGrounding, firstMatch_eq_none_iff]
  constructor
  · intro hscan hundischarged
    rcases hundischarged with ⟨clause, hclause, assignment, hbody, hhead⟩
    have hfalse := hscan (clause, assignment)
      ((mem_allGroundings).mpr hclause)
    rw [(eqGroundingUndischarged_eq_true_iff).mpr ⟨hbody, hhead⟩] at hfalse
    contradiction
  · intro hnone grounding hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hgrounding := eqGroundingUndischarged_eq_true_iff.mp htrue
    exact hnone ⟨grounding.1, (mem_allGroundings.mp hmem), grounding.2,
      hgrounding.1, hgrounding.2⟩

#print axioms selectEqClash_eq_none_iff
#print axioms selectEqClash_refutes
#print axioms selectEqClauseGrounding_eq_none_iff

end ContextCalculus.Hypertableau
