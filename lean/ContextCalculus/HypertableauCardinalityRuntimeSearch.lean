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

def DistinctEqState.CardinalityRuntimeTerminal
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : DistinctEqState Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop) : Prop :=
  state.EqualityApartClashFree ∧
  state.base.ClosedClashFree ∧
  ¬state.base.HasClosedUndischarged ontology ∧
  ¬state.base.HasUnblockedUnwitnessed parent ancestors ∧
  ¬state.HasExpandableMinimum definitions parent ancestors expanded ∧
  ¬state.HasViolatingMaximum definitions

/-- Exact terminal classification after all six ordered cardinality controls
are exhausted.  This theorem deliberately does not turn terminality into SAT:
blocked obligations and the finite quotient model still require their
independent executable certificate check. -/
theorem cardinalityRuntimeTerminal_iff_selectors_exhausted
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop) :
    state.CardinalityRuntimeTerminal ontology definitions parent ancestors expanded ↔
      selectEqualityApartClash state = none ∧
      selectCardinalityConceptClash state = none ∧
      selectCardinalityClauseGrounding ontology state = none ∧
      selectEqUnblockedUnwitnessed state.base parent ancestors = none ∧
      selectExpandableMinimum definitions state parent ancestors expanded = none ∧
      selectViolatingMaximum definitions state = none := by
  rw [DistinctEqState.CardinalityRuntimeTerminal,
    selectEqualityApartClash_eq_none_iff,
    selectCardinalityConceptClash_eq_none_iff,
    selectCardinalityClauseGrounding_eq_none_iff,
    selectEqUnblockedUnwitnessed_eq_none_iff,
    selectExpandableMinimum_eq_none_iff,
    selectViolatingMaximum_eq_none_iff]

theorem cardinalityRuntimeTerminal_of_selectors_exhausted
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState Node Concept Role)
    (parent : Node → Option Node) (ancestors : Node → List Node)
    (expanded : CardinalityDef Concept Role → Node → Prop)
    (hapart : selectEqualityApartClash state = none)
    (hclash : selectCardinalityConceptClash state = none)
    (hclause : selectCardinalityClauseGrounding ontology state = none)
    (hwitness : selectEqUnblockedUnwitnessed state.base parent ancestors = none)
    (hminimum : selectExpandableMinimum definitions state parent ancestors expanded = none)
    (hmaximum : selectViolatingMaximum definitions state = none) :
    state.CardinalityRuntimeTerminal ontology definitions parent ancestors expanded :=
  (cardinalityRuntimeTerminal_iff_selectors_exhausted ontology definitions state
    parent ancestors expanded).2
    ⟨hapart, hclash, hclause, hwitness, hminimum, hmaximum⟩

def FiniteEqCertificate.closedLabelB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (node : Fin nodeCount) (lit : Lit (Fin conceptCount)) : Bool :=
  certificate.base.labels.any fun entry =>
    decide (entry.2 = lit) && certificate.closedRelatedB entry.1 node

def FiniteEqCertificate.closedEdgeB
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (role : Fin roleCount) (source target : Fin nodeCount) : Bool :=
  certificate.base.edges.any fun entry =>
    decide (entry.1 = role) && certificate.closedRelatedB entry.2.1 source &&
      certificate.closedRelatedB entry.2.2 target

theorem FiniteEqCertificate.closedLabelB_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (node : Fin nodeCount) (lit : Lit (Fin conceptCount)) :
    certificate.closedLabelB node lit = true ↔ certificate.state.closedLabel node lit := by
  simp only [FiniteEqCertificate.closedLabelB, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨source, candidate⟩, hmem, rfl, hrelated⟩
    exact ⟨source, (certificate.closedRelatedB_eq_true hvalid source node).mp hrelated,
      hmem⟩
  · rintro ⟨source, hrelated, hmem⟩
    exact ⟨(source, lit), hmem, rfl,
      (certificate.closedRelatedB_eq_true hvalid source node).mpr hrelated⟩

theorem FiniteEqCertificate.closedEdgeB_eq_true_iff
    (certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount)
    (hvalid : certificate.equalityClosureValidB = true)
    (role : Fin roleCount) (source target : Fin nodeCount) :
    certificate.closedEdgeB role source target = true ↔
      certificate.state.closedEdge role source target := by
  simp only [FiniteEqCertificate.closedEdgeB, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨candidate, edgeSource, edgeTarget⟩, hmem,
      ⟨⟨rfl, hsource⟩, htarget⟩⟩
    exact ⟨edgeSource, edgeTarget,
      (certificate.closedRelatedB_eq_true hvalid edgeSource source).mp hsource,
      (certificate.closedRelatedB_eq_true hvalid edgeTarget target).mp htarget, hmem⟩
  · rintro ⟨edgeSource, edgeTarget, hsource, htarget, hmem⟩
    exact ⟨(role, edgeSource, edgeTarget), hmem,
      ⟨⟨rfl, (certificate.closedRelatedB_eq_true hvalid edgeSource source).mpr hsource⟩,
        (certificate.closedRelatedB_eq_true hvalid edgeTarget target).mpr htarget⟩⟩

/-- Checker matching Rust's quotient-closed distinct-cardinality recursion.
Unlike the legacy checker, clause bodies, maximum premises, and minimum markers
all use complete equality closure. -/
def FiniteDistinctCardinalityRefutationTree.checkClosed
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) :
    FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth → Bool
  | .equalityApart left right =>
      certificate.base.equalityClosureValidB &&
      certificate.base.closedRelatedB left right &&
      decide ((left, right) ∈ certificate.apart)
  | .equality tree => tree.checkClosed certificate.base
  | .clash => certificate.base.equalityClosureValidB && certificate.base.closedClashB
  | .delay child => child.checkClosed definitions certificate
  | .maximum definition source witnesses next children =>
      certificate.base.equalityClosureValidB &&
      decide (definition ∈ definitions) &&
      decide (definition.kind = .maximum) &&
      certificate.base.closedLabelB source (.pos definition.marker) &&
      (List.finRange (definition.bound + 1)).all fun index =>
        certificate.base.closedEdgeB definition.role source (witnesses index) &&
        certificate.base.closedLabelB (witnesses index) (.pos definition.filler) &&
        (List.finRange (definition.bound + 1)).all fun other =>
          decide (index = other) ||
          (certificate.mergeTransitionB (next index other)
              (witnesses index) (witnesses other) &&
            (children index other).checkClosed definitions (next index other))
  | .branch clause assignment next children =>
      certificate.base.equalityClosureValidB &&
      decide (clause ∈ certificate.base.base.ontology) &&
      clause.body.all (certificate.base.quotientClosedHoldsAtomB assignment) &&
      decide (∀ index,
        certificate.transitionB (next index) assignment (clause.head.get index) = true ∧
        (children index).checkClosed definitions (next index) = true)
  | .witness source target role filler child =>
      certificate.base.equalityClosureValidB &&
      decide ((role, filler, source) ∈ certificate.base.base.obligations) &&
      certificate.freshNodeB target &&
      child.checkClosed definitions
        (certificate.materializeWitness source target role filler)
  | .minimum definition source targets next child =>
      certificate.base.equalityClosureValidB &&
      decide (definition ∈ definitions) && decide (definition.kind = .minimum) &&
      certificate.base.closedLabelB source (.pos definition.marker) &&
      certificate.freshFamilyB targets &&
      certificate.minimumTransitionB next source targets definition.role definition.filler &&
      child.checkClosed definitions next

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_sound
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.checkClosed definitions certificate = true) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount)
      certificate.base.base.ontology definitions certificate.state := by
  induction tree generalizing certificate with
  | equality tree =>
      exact .equality certificate.state
        (tree.checkClosed_sound certificate.base
          (by simpa [FiniteDistinctCardinalityRefutationTree.checkClosed] using hcheck))
  | clash =>
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true] at hcheck
      exact .clash certificate.state
        (certificate.base.closedClashB_sound hcheck.1 hcheck.2)
  | equalityApart left right =>
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact .equalityApart certificate.state left right
        ((certificate.base.closedRelatedB_eq_true hcheck.1.1 left right).mp hcheck.1.2)
        hcheck.2
  | delay child ih =>
      exact ih certificate
        (by simpa [FiniteDistinctCardinalityRefutationTree.checkClosed] using hcheck)
  | maximum definition source witnesses next children ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, List.all_eq_true, List.mem_finRange,
        decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hsuccessors⟩
      apply ClosedDistinctCardinalityRefutes.maximum certificate.state definition
        hdefinition hkind source
        ((certificate.base.closedLabelB_eq_true_iff hvalid source
          (.pos definition.marker)).mp hmarker)
        witnesses
      · intro index
        exact (certificate.base.closedEdgeB_eq_true_iff hvalid definition.role source
          (witnesses index)).mp (hsuccessors index trivial).1.1
      · intro index
        exact (certificate.base.closedLabelB_eq_true_iff hvalid (witnesses index)
          (.pos definition.filler)).mp (hsuccessors index trivial).1.2
      · intro left right hne
        have hentry := (hsuccessors left trivial).2 right trivial
        have hchild :
            certificate.mergeTransitionB (next left right)
                (witnesses left) (witnesses right) = true ∧
              (children left right).checkClosed definitions (next left right) = true := by
          simpa [hne] using hentry
        rw [← certificate.mergeTransitionB_state (next left right)
          (witnesses left) (witnesses right) hchild.1]
        have htransition := hchild.1
        simp only [FiniteDistinctEqCertificate.mergeTransitionB, Bool.and_eq_true,
          FiniteEqCertificate.mergeTransitionB, decide_eq_true_eq] at htransition
        have hontology : (next left right).base.base.ontology =
            certificate.base.base.ontology := htransition.1.1.1.1.1
        simpa only [hontology] using ih left right (next left right) hchild.2
  | branch clause assignment next children ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hclause⟩, hbody⟩, hchildren⟩
      apply ClosedDistinctCardinalityRefutes.branch certificate.state clause hclause assignment
      · intro atom hatom
        exact (certificate.base.quotientClosedHoldsAtomB_eq_true hvalid assignment atom).mp
          (hbody atom hatom)
      · intro atom hatom
        rcases List.mem_iff_get.mp hatom with ⟨index, hindex⟩
        rw [← hindex]
        rcases hchildren index with ⟨htransition, hchild⟩
        rw [← certificate.transitionB_state (next index) assignment
          (clause.head.get index) htransition]
        have hparts := htransition
        simp only [FiniteDistinctEqCertificate.transitionB, Bool.and_eq_true,
          decide_eq_true_eq] at hparts
        have hbase := certificate.base.transitionB_base (next index).base assignment
          (clause.head.get index) hparts.1
        have hontology : (next index).base.base.ontology =
            certificate.base.base.ontology := by
          rw [hbase]
          cases clause.head.get index <;> rfl
        simpa only [hontology] using ih index (next index) hchild
  | witness source target role filler child ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with ⟨⟨⟨hvalid, hobligation⟩, hfresh⟩, hchild⟩
      apply ClosedDistinctCardinalityRefutes.witness certificate.state source target role filler
        hobligation (certificate.freshNodeB_sound target hvalid hfresh)
      rw [← certificate.state_materializeWitness source target role filler]
      exact ih (certificate.materializeWitness source target role filler) hchild
  | minimum definition source targets next child ih =>
      simp only [FiniteDistinctCardinalityRefutationTree.checkClosed,
        Bool.and_eq_true, decide_eq_true_eq] at hcheck
      rcases hcheck with
        ⟨⟨⟨⟨⟨⟨hvalid, hdefinition⟩, hkind⟩, hmarker⟩, hfresh⟩,
          htransition⟩, hchild⟩
      apply ClosedDistinctCardinalityRefutes.minimum certificate.state definition
        hdefinition hkind source
        ((certificate.base.closedLabelB_eq_true_iff hvalid source
          (.pos definition.marker)).mp hmarker)
        targets (certificate.freshFamilyB_sound targets hvalid hfresh)
      rw [← certificate.minimumTransitionB_state next source targets definition.role
        definition.filler htransition]
      have htransitionParts := htransition
      simp only [FiniteDistinctEqCertificate.minimumTransitionB, Bool.and_eq_true,
        FiniteEqCertificate.minimumTransitionB, decide_eq_true_eq] at htransitionParts
      have hontology : next.base.base.ontology = certificate.base.base.ontology :=
        htransitionParts.1.1.1.1.1
      simpa only [hontology] using ih next hchild

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_unsatisfiable
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬certificate.state.RealizableWithCardinality
      certificate.base.base.ontology definitions :=
  (tree.checkClosed_sound definitions certificate hcheck).sound

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_ontology_unsatisfiable
    [Nonempty (Fin nodeCount)]
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hempty : certificate.base.EmptyRoot) (hapart : certificate.apart = [])
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
      Nonempty Domain ∧ I.models certificate.base.base.ontology ∧
        I.modelsCardinalityDefs definitions := by
  rintro ⟨Domain, I, hdomain, hmodels, hcardinality⟩
  apply tree.checkClosed_unsatisfiable definitions certificate hcheck
  let value : Fin nodeCount → Domain := fun _ => Classical.choice hdomain
  refine ⟨Domain, I, value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hempty with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_⟩
    · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
        FiniteSatCertificate.state, State.RealizedBy, hlabels, hedges, hobligations]
    · intro left right _
      rfl
  · simp [FiniteDistinctEqCertificate.state, hapart]

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_subsumption
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (sub sup : Fin conceptCount)
    (hroot : certificate.base.SubsumptionRoot root sub sup)
    (hapart : certificate.apart = [])
    (hcheck : tree.checkClosed definitions certificate = true) :
    EntailsSubWithCardinality certificate.base.base.ontology definitions sub sup := by
  intro Domain I hmodels hcardinality value hsub
  by_contra hsup
  apply tree.checkClosed_unsatisfiable definitions certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro node lit hlabel
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hlabels, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq] at hlabel
        rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [Interp.satLit, Lit.pos] using hsub
        · simpa [Interp.satLit, Lit.negated] using hsup
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hedges]
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hobligations]
    · intro left right _
      rfl
  · simp [FiniteDistinctEqCertificate.state, hapart]

theorem FiniteDistinctCardinalityRefutationTree.checkClosed_unsatisfiable_concept
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (root : Fin nodeCount) (concept : Fin conceptCount)
    (hroot : certificate.base.UnsatisfiableRoot root concept)
    (hapart : certificate.apart = [])
    (hcheck : tree.checkClosed definitions certificate = true) :
    UnsatisfiableConceptWithCardinality certificate.base.base.ontology
      definitions concept := by
  intro Domain I hmodels hcardinality value hconcept
  apply tree.checkClosed_unsatisfiable definitions certificate hcheck
  refine ⟨Domain, I, fun _ => value, hmodels, hcardinality, ?_, ?_⟩
  · rcases hroot with ⟨hlabels, hedges, hobligations⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro node lit hlabel
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hlabels, List.mem_cons, List.not_mem_nil,
          or_false, Prod.mk.injEq] at hlabel
        rcases hlabel with ⟨rfl, rfl⟩
        simpa [Interp.satLit, Lit.pos] using hconcept
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hedges]
      · simp [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state, hobligations]
    · intro left right _
      rfl
  · simp [FiniteDistinctEqCertificate.state, hapart]

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
#print axioms cardinalityRuntimeTerminal_iff_selectors_exhausted
#print axioms cardinalityRuntimeTerminal_of_selectors_exhausted
#print axioms EqState.realized_closedLabel
#print axioms EqState.realized_closedEdge
#print axioms DistinctEqState.materializeMinimum_closed_realized
#print axioms ClosedDistinctCardinalityRefutes.sound
#print axioms DistinctCardinalityRefutes.toClosed
#print axioms FiniteEqCertificate.closedLabelB_eq_true_iff
#print axioms FiniteEqCertificate.closedEdgeB_eq_true_iff
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_sound
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_unsatisfiable
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_ontology_unsatisfiable
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_subsumption
#print axioms FiniteDistinctCardinalityRefutationTree.checkClosed_unsatisfiable_concept

end ContextCalculus.Hypertableau
