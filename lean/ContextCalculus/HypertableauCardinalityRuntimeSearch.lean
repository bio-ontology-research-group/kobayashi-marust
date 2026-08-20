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

theorem EqState.realized_closedLabel
    (state : EqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain)
    (hrealized : state.RealizedBy I value) (node : Node) (lit : Lit Concept)
    (hlabel : state.closedLabel node lit) : I.satLit lit (value node) := by
  rcases hlabel with ⟨source, hequiv, hsource⟩
  have hsatisfies := hrealized.1.1 source lit hsource
  rw [hrealized.2 source node hequiv] at hsatisfies
  exact hsatisfies

theorem EqState.realized_closedEdge
    (state : EqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain)
    (hrealized : state.RealizedBy I value) (role : Role) (source target : Node)
    (hedge : state.closedEdge role source target) :
    I.role role (value source) (value target) := by
  rcases hedge with ⟨edgeSource, edgeTarget, hsource, htarget, hedge⟩
  have hsatisfies := hrealized.1.2.1 role edgeSource edgeTarget hedge
  rw [hrealized.2 edgeSource source hsource,
    hrealized.2 edgeTarget target htarget] at hsatisfies
  exact hsatisfies

theorem DistinctEqState.materializeMinimum_closed_realized
    (state : DistinctEqState Node Concept Role)
    (I : Interp Domain Concept Role) (value : Node → Domain)
    (hrealized : state.RealizedBy I value)
    (source : Node) (targets : Fin count → Node) (role : Role) (filler marker : Concept)
    (hmarker : state.base.closedLabel source (.pos marker))
    (hfresh : state.FreshFamily targets)
    (witnesses : Fin count → Domain) (hinjective : Function.Injective witnesses)
    (hsuccessors : ∀ index, I.role role (value source) (witnesses index) ∧
      I.concept filler (witnesses index)) :
    ∃ value', (state.materializeMinimum source targets role filler).RealizedBy I value' := by
  rcases hmarker with ⟨markerSource, hequiv, hmarkerSource⟩
  have hsuccessors' : ∀ index,
      I.role role (value markerSource) (witnesses index) ∧
        I.concept filler (witnesses index) := by
    intro index
    rw [hrealized.1.2 markerSource source hequiv]
    exact hsuccessors index
  rcases state.materializeMinimum_realized I value hrealized markerSource targets role
      filler marker hmarkerSource hfresh witnesses hinjective hsuccessors' with
    ⟨value', hmaterialized⟩
  refine ⟨value', ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact hmaterialized.1.1.1
  · intro candidateRole candidateSource candidateTarget hedge
    rcases hedge with hedge | ⟨index, hrole, hsource, htarget⟩
    · exact hmaterialized.1.1.2.1 candidateRole candidateSource candidateTarget
        (Or.inl hedge)
    · have hedge' := hmaterialized.1.1.2.1 role markerSource (targets index)
          (Or.inr ⟨index, rfl, rfl, rfl⟩)
      have hvalue := hmaterialized.1.2 markerSource source hequiv
      rw [hvalue] at hedge'
      simpa [hrole, hsource, htarget] using hedge'
  · exact hmaterialized.1.1.2.2
  · exact hmaterialized.1.2
  · exact hmaterialized.2

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
      (source : Node) (hmarker : state.base.closedLabel source (.pos definition.marker))
      (witnesses : Fin (definition.bound + 1) → Node)
      (hedge : ∀ index,
        state.base.closedEdge definition.role source (witnesses index))
      (hfiller : ∀ index,
        state.base.closedLabel (witnesses index) (.pos definition.filler))
      (children : ∀ left right, left ≠ right →
        ClosedDistinctCardinalityRefutes Node ontology definitions
          (state.merge (witnesses left) (witnesses right))) :
      ClosedDistinctCardinalityRefutes Node ontology definitions state
  | minimum (state) (definition : CardinalityDef Concept Role)
      (hdefinition : definition ∈ definitions)
      (hkind : definition.kind = .minimum)
      (source : Node) (hmarker : state.base.closedLabel source (.pos definition.marker))
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
        state.base.realized_closedLabel I value hrealized.1 source
          (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      have hsuccessors : ∀ index,
          I.cardinalitySuccessor definition (value source) (value (witnesses index)) := by
        intro index
        exact ⟨state.base.realized_closedEdge I value hrealized.1 definition.role
            source (witnesses index) (hedge index),
          state.base.realized_closedLabel I value hrealized.1 (witnesses index)
            (.pos definition.filler) (hfiller index)⟩
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
        state.base.realized_closedLabel I value hrealized.1 source
          (.pos definition.marker) hmarker
      have hdefinitionModels : I.modelsCardinalityDef definition :=
        hcardinality definition hdefinition
      rcases I.minimum_witnesses definition hkind hdefinitionModels (value source)
          hmarkerSat with ⟨witnesses, hinjective, hsuccessors⟩
      rcases state.materializeMinimum_closed_realized I value hrealized source targets
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
      exact .maximum state definition hdefinition hkind source
        ⟨source, state.base.equiv_equivalence.refl source, hmarker⟩ witnesses
        (fun index => ⟨source, witnesses index,
          state.base.equiv_equivalence.refl source,
          state.base.equiv_equivalence.refl (witnesses index), hedge index⟩)
        (fun index => ⟨witnesses index,
          state.base.equiv_equivalence.refl (witnesses index), hfiller index⟩) ih
  | minimum state definition hdefinition hkind source hmarker targets hfresh child ih =>
      exact .minimum state definition hdefinition hkind source
        ⟨source, state.base.equiv_equivalence.refl source, hmarker⟩ targets hfresh ih

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

noncomputable def distinctFreshNodeBool
    (state : DistinctEqState Node Concept Role) (target : Node) : Bool := by
  classical
  exact decide (state.Fresh target)

@[simp] theorem distinctFreshNodeBool_eq_true_iff
    (state : DistinctEqState Node Concept Role) (target : Node) :
    distinctFreshNodeBool state target = true ↔ state.Fresh target := by
  simp [distinctFreshNodeBool]

noncomputable def selectDistinctFreshNode
    [Fintype Node] [DecidableEq Node]
    (state : DistinctEqState Node Concept Role) : Option Node :=
  firstMatch (distinctFreshNodeBool state) Finset.univ.toList

theorem selectDistinctFreshNode_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    (state : DistinctEqState Node Concept Role) :
    selectDistinctFreshNode state = none ↔ ¬∃ target, state.Fresh target := by
  classical
  rw [selectDistinctFreshNode, firstMatch_eq_none_iff]
  constructor
  · intro hscan hexists
    rcases hexists with ⟨target, hfresh⟩
    have hfalse := hscan target (by simp)
    rw [(distinctFreshNodeBool_eq_true_iff state target).mpr hfresh] at hfalse
    contradiction
  · intro hnone target _
    apply Bool.eq_false_iff.mpr
    intro htrue
    exact hnone ⟨target, (distinctFreshNodeBool_eq_true_iff state target).mp htrue⟩

/-- The fourth Rust control combines the quotient-blocked unwitnessed scan
with a fresh node that is also absent from every explicit disequality. -/
theorem selectCardinalityWitness_closedRefutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    {candidate : WitnessCandidate Node Concept Role}
    (hwitness : selectEqUnblockedUnwitnessed state.base parent ancestors = some candidate)
    {target : Node} (hfresh : selectDistinctFreshNode state = some target)
    (child : ClosedDistinctCardinalityRefutes Node ontology definitions
      (state.materializeWitness candidate.2.2 target candidate.1 candidate.2.1)) :
    ClosedDistinctCardinalityRefutes Node ontology definitions state := by
  classical
  have hcandidate := firstMatch_eq_some_mem
    (by simpa [selectEqUnblockedUnwitnessed] using hwitness)
  have hproperties :=
    (eqUnblockedWitnessCandidateBool_eq_true_iff state.base parent ancestors candidate).mp
      hcandidate.2
  have htarget := firstMatch_eq_some_mem
    (by simpa [selectDistinctFreshNode] using hfresh)
  exact .witness state candidate.2.2 target candidate.1 candidate.2.1
    hproperties.1 ((distinctFreshNodeBool_eq_true_iff state target).mp htarget.2) child

theorem selectCardinalityWitness_not_realizable
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    {candidate : WitnessCandidate Node Concept Role}
    (hwitness : selectEqUnblockedUnwitnessed state.base parent ancestors = some candidate)
    {target : Node} (hfresh : selectDistinctFreshNode state = some target)
    (child : ClosedDistinctCardinalityRefutes Node ontology definitions
      (state.materializeWitness candidate.2.2 target candidate.1 candidate.2.1)) :
    ¬state.RealizableWithCardinality ontology definitions :=
  (selectCardinalityWitness_closedRefutes ontology definitions state parent ancestors
    hwitness hfresh child).sound

abbrev MinimumCandidate (Node Concept Role : Type) :=
  CardinalityDef Concept Role × Node

noncomputable def allMinimumCandidates
    [Fintype Node] [DecidableEq Node]
    (definitions : List (CardinalityDef Concept Role)) :
    List (MinimumCandidate Node Concept Role) :=
  definitions.flatMap fun definition =>
    (Finset.univ.toList : List Node).map fun source => (definition, source)

theorem mem_allMinimumCandidates
    [Fintype Node] [DecidableEq Node]
    {definitions : List (CardinalityDef Concept Role)}
    {candidate : MinimumCandidate Node Concept Role} :
    candidate ∈ allMinimumCandidates definitions ↔ candidate.1 ∈ definitions := by
  classical
  rcases candidate with ⟨definition, source⟩
  simp [allMinimumCandidates]

noncomputable def minimumCandidateBool
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop)
    (candidate : MinimumCandidate Node Concept Role) : Bool := by
  classical
  exact decide (candidate.1.kind = .minimum) &&
    decide (state.base.closedLabel candidate.2 (.pos candidate.1.marker)) &&
    decide (¬expanded candidate.1 candidate.2) &&
    !(quotientBlockedBool state.base parent ancestors candidate.2)

theorem minimumCandidateBool_eq_true_iff
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop)
    (candidate : MinimumCandidate Node Concept Role) :
    minimumCandidateBool state parent ancestors expanded candidate = true ↔
      candidate.1.kind = .minimum ∧
      state.base.closedLabel candidate.2 (.pos candidate.1.marker) ∧
      ¬expanded candidate.1 candidate.2 ∧
      quotientBlockedBool state.base parent ancestors candidate.2 = false := by
  classical
  simp [minimumCandidateBool, and_assoc]

noncomputable def selectExpandableMinimum
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop) :
    Option (MinimumCandidate Node Concept Role) :=
  firstMatch (minimumCandidateBool state parent ancestors expanded)
    (allMinimumCandidates definitions)

def DistinctEqState.HasExpandableMinimum
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : DistinctEqState Node Concept Role)
    (definitions : List (CardinalityDef Concept Role))
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop) : Prop :=
  ∃ definition ∈ definitions, ∃ source,
    definition.kind = .minimum ∧
    state.base.closedLabel source (.pos definition.marker) ∧
    ¬expanded definition source ∧
    quotientBlockedBool state.base parent ancestors source = false

theorem selectExpandableMinimum_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop) :
    selectExpandableMinimum definitions state parent ancestors expanded = none ↔
      ¬state.HasExpandableMinimum definitions parent ancestors expanded := by
  classical
  rw [selectExpandableMinimum, firstMatch_eq_none_iff]
  constructor
  · intro hscan hexists
    rcases hexists with
      ⟨definition, hdefinition, source, hkind, hmarker, hexpanded, hunblocked⟩
    have hfalse := hscan (definition, source)
      ((mem_allMinimumCandidates).mpr hdefinition)
    rw [(minimumCandidateBool_eq_true_iff state parent ancestors expanded _).mpr
      ⟨hkind, hmarker, hexpanded, hunblocked⟩] at hfalse
    contradiction
  · intro hnone candidate hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hproperties :=
      (minimumCandidateBool_eq_true_iff state parent ancestors expanded candidate).mp htrue
    exact hnone ⟨candidate.1, (mem_allMinimumCandidates.mp hmem), candidate.2,
      hproperties.1, hproperties.2.1, hproperties.2.2.1, hproperties.2.2.2⟩

theorem selectExpandableMinimum_closedRefutes
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop)
    {candidate : MinimumCandidate Node Concept Role}
    (hselect : selectExpandableMinimum definitions state parent ancestors expanded =
      some candidate)
    (targets : Fin candidate.1.bound → Node)
    (hfresh : state.FreshFamily targets)
    (child : ClosedDistinctCardinalityRefutes Node ontology definitions
      (state.materializeMinimum candidate.2 targets candidate.1.role candidate.1.filler)) :
    ClosedDistinctCardinalityRefutes Node ontology definitions state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectExpandableMinimum] using hselect)
  have hproperties :=
    (minimumCandidateBool_eq_true_iff state parent ancestors expanded candidate).mp
      hfound.2
  exact .minimum state candidate.1 (mem_allMinimumCandidates.mp hfound.1)
    hproperties.1 candidate.2 hproperties.2.1 targets hfresh child

abbrev MaximumCandidate (Node Concept Role : Type) :=
  Σ definition : CardinalityDef Concept Role,
    Node × (Fin (definition.bound + 1) → Node)

noncomputable def allMaximumCandidates
    [Fintype Node] [DecidableEq Node]
    (definitions : List (CardinalityDef Concept Role)) :
    List (MaximumCandidate Node Concept Role) := by
  classical
  exact definitions.flatMap fun definition =>
    (Finset.univ.toList : List Node).flatMap fun source =>
      (Finset.univ.toList : List (Fin (definition.bound + 1) → Node)).map
        fun witnesses => ⟨definition, source, witnesses⟩

theorem mem_allMaximumCandidates_definition
    [Fintype Node] [DecidableEq Node]
    {definitions : List (CardinalityDef Concept Role)}
    {candidate : MaximumCandidate Node Concept Role}
    (hmem : candidate ∈ allMaximumCandidates definitions) :
    candidate.1 ∈ definitions := by
  classical
  simp only [allMaximumCandidates, List.mem_flatMap, List.mem_map] at hmem
  rcases hmem with ⟨definition, hdefinition, source, _, witnesses, _, heq⟩
  have hfirst := congrArg Sigma.fst heq
  simpa using hfirst.symm ▸ hdefinition

theorem maximumCandidate_mem_all
    [Fintype Node] [DecidableEq Node]
    (definitions : List (CardinalityDef Concept Role))
    (definition : CardinalityDef Concept Role) (hdefinition : definition ∈ definitions)
    (source : Node) (witnesses : Fin (definition.bound + 1) → Node) :
    (⟨definition, source, witnesses⟩ : MaximumCandidate Node Concept Role) ∈
      allMaximumCandidates definitions := by
  classical
  simp [allMaximumCandidates, hdefinition]

noncomputable def maximumCandidateBool
    (state : DistinctEqState Node Concept Role)
    (candidate : MaximumCandidate Node Concept Role) : Bool := by
  classical
  exact decide (candidate.1.kind = .maximum) &&
    decide (state.base.closedLabel candidate.2.1 (.pos candidate.1.marker)) &&
    decide (∀ index,
      state.base.closedEdge candidate.1.role candidate.2.1 (candidate.2.2 index) ∧
      state.base.closedLabel (candidate.2.2 index) (.pos candidate.1.filler)) &&
    decide (∀ left right, left ≠ right →
      ¬state.base.equiv (candidate.2.2 left) (candidate.2.2 right))

theorem maximumCandidateBool_eq_true_iff
    (state : DistinctEqState Node Concept Role)
    (candidate : MaximumCandidate Node Concept Role) :
    maximumCandidateBool state candidate = true ↔
      candidate.1.kind = .maximum ∧
      state.base.closedLabel candidate.2.1 (.pos candidate.1.marker) ∧
      (∀ index,
        state.base.closedEdge candidate.1.role candidate.2.1 (candidate.2.2 index) ∧
        state.base.closedLabel (candidate.2.2 index) (.pos candidate.1.filler)) ∧
      ∀ left right, left ≠ right →
        ¬state.base.equiv (candidate.2.2 left) (candidate.2.2 right) := by
  classical
  simp [maximumCandidateBool, and_assoc]

noncomputable def selectViolatingMaximum
    [Fintype Node] [DecidableEq Node]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role) :
    Option (MaximumCandidate Node Concept Role) :=
  firstMatch (maximumCandidateBool state) (allMaximumCandidates definitions)

def DistinctEqState.HasViolatingMaximum
    (state : DistinctEqState Node Concept Role)
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ definition ∈ definitions, ∃ source,
    ∃ witnesses : Fin (definition.bound + 1) → Node,
      definition.kind = .maximum ∧
      state.base.closedLabel source (.pos definition.marker) ∧
      (∀ index,
        state.base.closedEdge definition.role source (witnesses index) ∧
        state.base.closedLabel (witnesses index) (.pos definition.filler)) ∧
      ∀ left right, left ≠ right →
        ¬state.base.equiv (witnesses left) (witnesses right)

theorem selectViolatingMaximum_eq_none_iff
    [Fintype Node] [DecidableEq Node]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role) :
    selectViolatingMaximum definitions state = none ↔
      ¬state.HasViolatingMaximum definitions := by
  classical
  rw [selectViolatingMaximum, firstMatch_eq_none_iff]
  constructor
  · intro hscan hexists
    rcases hexists with
      ⟨definition, hdefinition, source, witnesses, hkind, hmarker,
        hsuccessors, hdistinct⟩
    have hfalse := hscan
      (⟨definition, source, witnesses⟩ : MaximumCandidate Node Concept Role)
      (maximumCandidate_mem_all definitions definition hdefinition source witnesses)
    rw [(maximumCandidateBool_eq_true_iff state _).mpr
      ⟨hkind, hmarker, hsuccessors, hdistinct⟩] at hfalse
    contradiction
  · intro hnone candidate hmem
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hproperties := (maximumCandidateBool_eq_true_iff state candidate).mp htrue
    exact hnone ⟨candidate.1, mem_allMaximumCandidates_definition hmem,
      candidate.2.1, candidate.2.2, hproperties.1, hproperties.2.1,
      hproperties.2.2.1, hproperties.2.2.2⟩

theorem selectViolatingMaximum_closedRefutes
    [Fintype Node] [DecidableEq Node]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    {candidate : MaximumCandidate Node Concept Role}
    (hselect : selectViolatingMaximum definitions state = some candidate)
    (children : ∀ left right, left ≠ right →
      ClosedDistinctCardinalityRefutes Node ontology definitions
        (state.merge (candidate.2.2 left) (candidate.2.2 right))) :
    ClosedDistinctCardinalityRefutes Node ontology definitions state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectViolatingMaximum] using hselect)
  have hproperties := (maximumCandidateBool_eq_true_iff state candidate).mp hfound.2
  exact .maximum state candidate.1 (mem_allMaximumCandidates_definition hfound.1)
    hproperties.1 candidate.2.1 hproperties.2.1 candidate.2.2
    (fun index => (hproperties.2.2.1 index).1)
    (fun index => (hproperties.2.2.1 index).2) children

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
#print axioms selectDistinctFreshNode_eq_none_iff
#print axioms selectCardinalityWitness_closedRefutes
#print axioms selectCardinalityWitness_not_realizable
#print axioms selectExpandableMinimum_eq_none_iff
#print axioms selectExpandableMinimum_closedRefutes
#print axioms selectViolatingMaximum_eq_none_iff
#print axioms selectViolatingMaximum_closedRefutes
#print axioms EqState.realized_closedLabel
#print axioms EqState.realized_closedEdge
#print axioms DistinctEqState.materializeMinimum_closed_realized
#print axioms ClosedDistinctCardinalityRefutes.sound
#print axioms DistinctCardinalityRefutes.toClosed

end ContextCalculus.Hypertableau
