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

/-- Cardinality refutations whose clause bodies use the same complete quotient
closure as Rust's `closed_holds`.  The remaining constructors are the ordinary
distinct-cardinality rules. -/
inductive ClosedDistinctCardinalityRefutes (Node : Type u)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) :
    DistinctEqState Node Concept Role → Prop where
  | equality (state) (tree : ClosedEqRefutes Node ontology state.base) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | clash (state)
      (hclash : ∃ positiveNode negativeNode concept,
        state.base.equiv positiveNode negativeNode ∧
          state.base.base.label positiveNode (.pos concept) ∧
          state.base.base.label negativeNode (.negated concept)) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | branch (state) (clause : Clause Variable Concept Role)
      (hclause : clause ∈ ontology) (assignment : Variable → Node)
      (hbody : ∀ atom ∈ clause.body,
        state.base.closedHoldsAtom assignment atom)
      (children : ∀ atom, atom ∈ clause.head →
        ClosedDistinctCardinalityRefutes Node ontology definitions
          (state.assertAtom assignment atom)) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | witness (state) (source target : Node) (role : Role) (filler : Lit Concept)
      (hobligation : state.base.base.obligation role filler source)
      (hfresh : state.Fresh target)
      (child : ClosedDistinctCardinalityRefutes Node ontology definitions
        (state.materializeWitness source target role filler)) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | equalityApart (state) (left right : Node)
      (hequal : state.base.equiv left right)
      (hapart : state.apart left right) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | maximum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .maximum)
      (source : Node) (hmarker : state.base.base.label source (.pos definition.marker))
      (witnesses : Fin (definition.bound + 1) → Node)
      (hedge : ∀ index,
        state.base.base.edge definition.role source (witnesses index))
      (hfiller : ∀ index,
        state.base.base.label (witnesses index) (.pos definition.filler))
      (children : ∀ left right, left ≠ right →
        ClosedDistinctCardinalityRefutes Node ontology definitions
          (state.merge (witnesses left) (witnesses right))) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | minimum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .minimum)
      (source : Node) (hmarker : state.base.base.label source (.pos definition.marker))
      (targets : Fin definition.bound → Node)
      (hfresh : state.FreshFamily targets)
      (child : ClosedDistinctCardinalityRefutes Node ontology definitions
        (state.materializeMinimum source targets definition.role definition.filler)) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state

theorem ClosedDistinctCardinalityRefutes.sound
    (hrefutes : ClosedDistinctCardinalityRefutes Node ontology definitions state) :
    ¬state.RealizableWithCardinality ontology definitions := by
  induction hrefutes with
  | equality state tree =>
      rintro ⟨Domain, I, value, hmodels, _, hrealized⟩
      exact tree.sound ⟨Domain, I, value, hmodels, hrealized.1⟩
  | clash state hclash =>
      rintro ⟨Domain, I, value, _, _, hrealized⟩
      rcases hclash with
        ⟨positiveNode, negativeNode, concept, hequiv, hpositive, hnegative⟩
      have hpositiveSat := hrealized.1.1.1 positiveNode (.pos concept) hpositive
      have hnegativeSat := hrealized.1.1.1 negativeNode (.negated concept) hnegative
      rw [← hrealized.1.2 positiveNode negativeNode hequiv] at hnegativeSat
      exact hnegativeSat hpositiveSat
  | branch state clause hclause assignment hbody children ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      have hsemanticBody : ∀ atom ∈ clause.body,
          I.satAtom (value ∘ assignment) atom := by
        intro atom hatom
        exact state.base.realized_closedHoldsAtom I value hrealized.1 assignment atom
          (hbody atom hatom)
      rcases hmodels clause hclause (value ∘ assignment) hsemanticBody with
        ⟨atom, hatom, hsat⟩
      exact ih atom hatom ⟨Domain, I, value, hmodels, hcardinality,
        state.base.assertAtom_realized I value hrealized.1 assignment atom hsat,
        hrealized.2⟩
  | witness state source target role filler hobligation hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      rcases state.materializeWitness_realized I value hrealized source target role filler
          hobligation hfresh with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hcardinality, hchild⟩
  | equalityApart state left right hequal hapart =>
      exact state.equality_apart_clash left right hequal hapart
  | maximum state definition hdefinition hkind source hmarker witnesses
      hedge hfiller children ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      have hmarkerSat : I.concept definition.marker (value source) :=
        hrealized.1.1.1 source (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      have hsuccessors : ∀ index,
          I.cardinalitySuccessor definition (value source) (value (witnesses index)) := by
        intro index
        exact ⟨hrealized.1.1.2.1 definition.role source (witnesses index) (hedge index),
          hrealized.1.1.1 (witnesses index) (.pos definition.filler) (hfiller index)⟩
      have hnotInjective :
          ¬Function.Injective (fun index => value (witnesses index)) :=
        Interp.maximum_forces_merge (I := I) definition hkind
          hdefinitionModels (value source) hmarkerSat
          (fun index => value (witnesses index)) hsuccessors
      have hpair : ∃ left right, left ≠ right ∧
          value (witnesses left) = value (witnesses right) := by
        by_contra hnone
        push Not at hnone
        apply hnotInjective
        intro left right hequal
        by_contra hne
        exact hnone left right hne hequal
      rcases hpair with ⟨left, right, hne, hequal⟩
      exact ih left right hne ⟨Domain, I, value, hmodels, hcardinality,
        state.merge_realized I value hrealized (witnesses left) (witnesses right) hequal⟩
  | minimum state definition hdefinition hkind source hmarker targets hfresh child ih =>
      rintro ⟨Domain, I, value, hmodels, hcardinality, hrealized⟩
      have hmarkerSat : I.concept definition.marker (value source) :=
        hrealized.1.1.1 source (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      rcases I.minimum_witnesses definition hkind hdefinitionModels (value source)
          hmarkerSat with ⟨witnesses, hinjective, hsuccessors⟩
      rcases state.materializeMinimum_realized I value hrealized source targets
          definition.role definition.filler definition.marker hmarker hfresh witnesses
          hinjective hsuccessors with ⟨value', hchild⟩
      exact ih ⟨Domain, I, value', hmodels, hcardinality, hchild⟩

theorem DistinctCardinalityRefutes.toClosed
    (hrefutes : DistinctCardinalityRefutes Node ontology definitions state) :
    ClosedDistinctCardinalityRefutes Node ontology definitions state := by
  induction hrefutes with
  | equality state tree => exact .equality state tree.toClosed
  | clash state hclash => exact .clash state hclash
  | branch state clause hclause assignment hbody children ih =>
      exact .branch state clause hclause assignment
        (fun atom hatom => state.base.holdsAtom_implies_closedHoldsAtom assignment atom
          (hbody atom hatom)) ih
  | witness state source target role filler hobligation hfresh child ih =>
      exact .witness state source target role filler hobligation hfresh ih
  | equalityApart state left right hequal hapart =>
      exact .equalityApart state left right hequal hapart
  | maximum state definition hdefinition hkind source hmarker witnesses hedge hfiller
      children ih =>
      exact .maximum state definition hdefinition hkind source hmarker witnesses hedge
        hfiller ih
  | minimum state definition hdefinition hkind source hmarker targets hfresh child ih =>
      exact .minimum state definition hdefinition hkind source hmarker targets hfresh ih

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

/-- The third Rust control scans clauses and finite assignments using complete
quotient closure. -/
noncomputable def selectCardinalityClauseGrounding
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : DistinctEqState Node Concept Role) :
    Option (Grounding Variable Node Concept Role) :=
  selectEqClauseGrounding ontology state.base

theorem selectCardinalityClauseGrounding_eq_none_iff
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (state : DistinctEqState Node Concept Role) :
    selectCardinalityClauseGrounding ontology state = none ↔
      ¬state.base.HasClosedUndischarged ontology :=
  selectEqClauseGrounding_eq_none_iff ontology state.base

theorem selectCardinalityClauseGrounding_closedRefutes
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {grounding : Grounding Variable Node Concept Role}
    (hselect : selectCardinalityClauseGrounding ontology state = some grounding)
    (children : ∀ atom, atom ∈ grounding.1.head →
      ClosedDistinctCardinalityRefutes Node ontology definitions
        (state.assertAtom grounding.2 atom)) :
    ClosedDistinctCardinalityRefutes Node ontology definitions state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectCardinalityClauseGrounding, selectEqClauseGrounding] using hselect)
  have hproperties := eqGroundingUndischarged_eq_true_iff.mp hfound.2
  exact .branch state grounding.1 (mem_allGroundings.mp hfound.1)
    grounding.2 hproperties.1 children

theorem selectCardinalityClauseGrounding_not_realizable
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {grounding : Grounding Variable Node Concept Role}
    (hselect : selectCardinalityClauseGrounding ontology state = some grounding)
    (children : ∀ atom, atom ∈ grounding.1.head →
      ClosedDistinctCardinalityRefutes Node ontology definitions
        (state.assertAtom grounding.2 atom)) :
    ¬state.RealizableWithCardinality ontology definitions :=
  (selectCardinalityClauseGrounding_closedRefutes ontology definitions state
    hselect children).sound

#print axioms selectEqualityApartClash_eq_none_iff
#print axioms selectEqualityApartClash_refutes
#print axioms selectEqualityApartClash_not_realizable
#print axioms selectFiniteEqualityApartClash_eq_none_iff
#print axioms selectFiniteEqualityApartClash_refutes
#print axioms selectFiniteEqualityApartClash_not_realizable
#print axioms selectCardinalityConceptClash_eq_none_iff
#print axioms selectCardinalityConceptClash_refutes
#print axioms selectCardinalityConceptClash_not_realizable
#print axioms selectCardinalityClauseGrounding_eq_none_iff
#print axioms selectCardinalityClauseGrounding_closedRefutes
#print axioms selectCardinalityClauseGrounding_not_realizable
#print axioms ClosedDistinctCardinalityRefutes.sound
#print axioms DistinctCardinalityRefutes.toClosed

end ContextCalculus.Hypertableau
