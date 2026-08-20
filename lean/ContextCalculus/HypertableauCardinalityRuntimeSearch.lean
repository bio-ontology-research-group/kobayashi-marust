import ContextCalculus.HypertableauCardinalityDistinctCertificate
import ContextCalculus.HypertableauEqualityRuntimeSearch

/-!
# Executable cardinality-aware hypertableau runtime selection

This module begins the refinement of Rust's distinct-cardinality recursion in
the exact order used by `lean_distinct_cardinality_refutation`.  Its first
control scans the finite node square for an equality class that intersects the
explicit `apart` relation.  Finding one constructs the corresponding semantic
refutation; exhausting the scan proves that no such clash exists.
-/

namespace ContextCalculus.Hypertableau

abbrev EqualityApartCandidate (Node : Type) := Node × Node

noncomputable def allEqualityApartCandidates
    [Fintype Node] [DecidableEq Node] :
    List (EqualityApartCandidate Node) := by
  classical
  exact (Finset.univ.toList : List Node).flatMap fun left =>
    (Finset.univ.toList : List Node).map fun right => (left, right)

theorem mem_allEqualityApartCandidates
    [Fintype Node] [DecidableEq Node]
    (candidate : EqualityApartCandidate Node) :
    candidate ∈ allEqualityApartCandidates := by
  classical
  rcases candidate with ⟨left, right⟩
  simp [allEqualityApartCandidates]

noncomputable def equalityApartCandidateBool
    (state : DistinctEqState Node Concept Role)
    (candidate : EqualityApartCandidate Node) : Bool := by
  classical
  exact decide (state.base.equiv candidate.1 candidate.2) &&
    decide (state.apart candidate.1 candidate.2)

theorem equalityApartCandidateBool_eq_true_iff
    (state : DistinctEqState Node Concept Role)
    (candidate : EqualityApartCandidate Node) :
    equalityApartCandidateBool state candidate = true ↔
      state.base.equiv candidate.1 candidate.2 ∧
      state.apart candidate.1 candidate.2 := by
  simp [equalityApartCandidateBool]

noncomputable def selectEqualityApartClash
    [Fintype Node] [DecidableEq Node]
    (state : DistinctEqState Node Concept Role) :
    Option (EqualityApartCandidate Node) :=
  firstMatch (equalityApartCandidateBool state) allEqualityApartCandidates

def DistinctEqState.EqualityApartClashFree
    (state : DistinctEqState Node Concept Role) : Prop :=
  ∀ left right, state.base.equiv left right → ¬state.apart left right

theorem selectEqualityApartClash_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    (state : DistinctEqState Node Concept Role) :
    selectEqualityApartClash state = none ↔ state.EqualityApartClashFree := by
  classical
  rw [selectEqualityApartClash, firstMatch_eq_none_iff]
  constructor
  · intro hscan left right hequiv hapart
    have hfalse := hscan (left, right)
      (mem_allEqualityApartCandidates (left, right))
    rw [(equalityApartCandidateBool_eq_true_iff state _).mpr
      ⟨hequiv, hapart⟩] at hfalse
    contradiction
  · intro hfree candidate _
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hclash :=
      (equalityApartCandidateBool_eq_true_iff state candidate).mp htrue
    exact hfree candidate.1 candidate.2 hclash.1 hclash.2

theorem selectEqualityApartClash_refutes
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {candidate : EqualityApartCandidate Node}
    (hselect : selectEqualityApartClash state = some candidate) :
    DistinctCardinalityRefutes Node ontology definitions state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectEqualityApartClash] using hselect)
  have hclash :=
    (equalityApartCandidateBool_eq_true_iff state candidate).mp hfound.2
  exact .equalityApart state candidate.1 candidate.2 hclash.1 hclash.2

theorem selectEqualityApartClash_not_realizable
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {candidate : EqualityApartCandidate Node}
    (hselect : selectEqualityApartClash state = some candidate) :
    ¬state.RealizableWithCardinality ontology definitions :=
  (selectEqualityApartClash_refutes ontology definitions state hselect).sound

/-- The exact finite-list scan used by Rust's `equality_apart_clash`: inspect
the serialized `apart` pairs in order and return the first pair whose endpoints
have the same canonical representative. -/
noncomputable def selectFiniteEqualityApartClash
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    Option (Fin nodeCount × Fin nodeCount) := by
  classical
  exact firstMatch
    (fun pair => decide (certificate.base.state.equiv pair.1 pair.2))
    certificate.apart

theorem selectFiniteEqualityApartClash_eq_none_iff
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    selectFiniteEqualityApartClash certificate = none ↔
      certificate.state.EqualityApartClashFree := by
  classical
  rw [selectFiniteEqualityApartClash, firstMatch_eq_none_iff]
  constructor
  · intro hscan left right hequiv hapart
    change (left, right) ∈ certificate.apart at hapart
    have hfalse := hscan (left, right) hapart
    have hnot : ¬certificate.base.state.equiv left right := by
      simpa using (Bool.eq_false_iff.mp hfalse)
    exact hnot hequiv
  · intro hfree candidate hmem
    apply Bool.eq_false_iff.mpr
    intro hequiv
    exact hfree candidate.1 candidate.2 (by simpa using hequiv) hmem

theorem selectFiniteEqualityApartClash_refutes
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    {candidate : Fin nodeCount × Fin nodeCount}
    (hselect : selectFiniteEqualityApartClash certificate = some candidate) :
    DistinctCardinalityRefutes (Fin nodeCount) ontology definitions
      certificate.state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectFiniteEqualityApartClash] using hselect)
  exact .equalityApart certificate.state candidate.1 candidate.2
    (by simpa using hfound.2) hfound.1

theorem selectFiniteEqualityApartClash_not_realizable
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    {candidate : Fin nodeCount × Fin nodeCount}
    (hselect : selectFiniteEqualityApartClash certificate = some candidate) :
    ¬certificate.state.RealizableWithCardinality ontology definitions :=
  (selectFiniteEqualityApartClash_refutes ontology definitions certificate hselect).sound

/-- The second Rust control reuses the equality-aware concept-clash scan after
the equality/apart scan.  A selected quotient clash lifts directly into the
distinct-cardinality calculus. -/
noncomputable def selectCardinalityConceptClash
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : DistinctEqState Node Concept Role) :
    Option (EqClashCandidate Node Concept) :=
  selectEqClash state.base

theorem selectCardinalityConceptClash_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (state : DistinctEqState Node Concept Role) :
    selectCardinalityConceptClash state = none ↔ state.base.ClosedClashFree := by
  exact selectEqClash_eq_none_iff state.base

theorem selectCardinalityConceptClash_refutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {candidate : EqClashCandidate Node Concept}
    (hselect : selectCardinalityConceptClash state = some candidate) :
    DistinctCardinalityRefutes Node ontology definitions state := by
  exact .equality state (selectEqClash_refutes ontology state.base hselect)

theorem selectCardinalityConceptClash_not_realizable
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {candidate : EqClashCandidate Node Concept}
    (hselect : selectCardinalityConceptClash state = some candidate) :
    ¬state.RealizableWithCardinality ontology definitions :=
  (selectCardinalityConceptClash_refutes ontology definitions state hselect).sound

#print axioms selectEqualityApartClash_eq_none_iff
#print axioms selectEqualityApartClash_refutes
#print axioms selectEqualityApartClash_not_realizable
#print axioms selectFiniteEqualityApartClash_eq_none_iff
#print axioms selectFiniteEqualityApartClash_refutes
#print axioms selectFiniteEqualityApartClash_not_realizable
#print axioms selectCardinalityConceptClash_eq_none_iff
#print axioms selectCardinalityConceptClash_refutes
#print axioms selectCardinalityConceptClash_not_realizable

end ContextCalculus.Hypertableau
