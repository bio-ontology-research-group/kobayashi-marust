import ContextCalculus.HypertableauCardinalityRuntimeSearch

/-!
# Production-shaped cardinality hypertableau expansion

This module packages the six cardinality runtime controls into one typed
first-obstruction layer.  Each recursive constructor carries the exact selected
site and the earlier-selector exhaustion facts that establish production
priority.  Witness and minimum allocation use Rust's active-prefix IDs;
maximum expansion uses the deterministic greedy prefix vector.
-/

namespace ContextCalculus.Hypertableau

abbrev IndexedCardinalitySite (definitions : List (CardinalityDef Concept Role))
    (nodeCount : Nat) := Fin definitions.length × Fin nodeCount

/-- Rust scans definition IDs in stored order, then active source IDs.  The
active-prefix theorem later shows that extending this list to the finite node
budget does not introduce a selectable inactive source. -/
def allIndexedCardinalitySites
    (definitions : List (CardinalityDef Concept Role)) (nodeCount : Nat) :
    List (IndexedCardinalitySite definitions nodeCount) :=
  (List.finRange definitions.length).flatMap fun definitionId =>
    (List.finRange nodeCount).map fun source => (definitionId, source)

theorem mem_allIndexedCardinalitySites
    {definitions : List (CardinalityDef Concept Role)}
    {site : IndexedCardinalitySite definitions nodeCount} :
    site ∈ allIndexedCardinalitySites definitions nodeCount := by
  rcases site with ⟨definitionId, source⟩
  simp [allIndexedCardinalitySites]

noncomputable def indexedMinimumSiteBool
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount))
    (site : IndexedCardinalitySite definitions nodeCount) : Bool :=
  minimumCandidateBool state parent ancestors
    (fun _ source => ∃ expandedSource,
      (site.1, expandedSource) ∈ expanded ∧ state.base.equiv expandedSource source)
    (definitions.get site.1, site.2)

theorem indexedMinimumSiteBool_eq_true_iff
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount))
    (site : IndexedCardinalitySite definitions nodeCount) :
    indexedMinimumSiteBool definitions state parent ancestors expanded site = true ↔
      (definitions.get site.1).kind = .minimum ∧
      state.base.closedLabel site.2 (.pos (definitions.get site.1).marker) ∧
      (¬∃ expandedSource, (site.1, expandedSource) ∈ expanded ∧
        state.base.equiv expandedSource site.2) ∧
      quotientBlockedBool state.base parent ancestors site.2 = false := by
  simp [indexedMinimumSiteBool, minimumCandidateBool_eq_true_iff]

noncomputable def selectIndexedExpandableMinimum
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount)) :
    Option (IndexedCardinalitySite definitions nodeCount) :=
  firstMatch (indexedMinimumSiteBool definitions state parent ancestors expanded)
    (allIndexedCardinalitySites definitions nodeCount)

theorem selectIndexedExpandableMinimum_eq_none_iff
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount)) :
    selectIndexedExpandableMinimum definitions state parent ancestors expanded = none ↔
      ∀ site, indexedMinimumSiteBool definitions state parent ancestors expanded site = false := by
  rw [selectIndexedExpandableMinimum, firstMatch_eq_none_iff]
  constructor
  · intro hscan site
    exact hscan site mem_allIndexedCardinalitySites
  · intro hscan site _
    exact hscan site

theorem selectIndexedExpandableMinimum_closedRefutes
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount))
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedExpandableMinimum definitions state parent ancestors expanded =
      some site)
    (active : Nat) (hprefix : state.InactivePrefixFresh active)
    (hfit : active + (definitions.get site.1).bound ≤ nodeCount)
    (child : ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
      (state.materializeMinimum site.2
        (rustConsecutiveTargets active (definitions.get site.1).bound nodeCount hfit)
        (definitions.get site.1).role (definitions.get site.1).filler)) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectIndexedExpandableMinimum] using hselect)
  have hproperties := (indexedMinimumSiteBool_eq_true_iff definitions state parent ancestors
    expanded site).mp hfound.2
  exact .minimum state (definitions.get site.1) (List.get_mem definitions site.1)
    hproperties.1 site.2 hproperties.2.1
    (rustConsecutiveTargets active (definitions.get site.1).bound nodeCount hfit)
    (rustConsecutiveTargets_freshFamily state hprefix hfit) child

theorem selectIndexedExpandableMinimum_source_lt_active
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount))
    (active : Nat) (hprefix : state.InactivePrefixFresh active)
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedExpandableMinimum definitions state parent ancestors expanded =
      some site) : site.2.1 < active := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectIndexedExpandableMinimum] using hselect)
  have hproperties := (indexedMinimumSiteBool_eq_true_iff definitions state parent ancestors
    expanded site).mp hfound.2
  exact state.lt_active_of_closedLabel active hprefix site.2
    (.pos (definitions.get site.1).marker) hproperties.2.1

noncomputable def indexedMaximumSiteBool
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (site : IndexedCardinalitySite definitions nodeCount) : Bool :=
  rustMaximumSiteBool state (definitions.get site.1, site.2)

theorem indexedMaximumSiteBool_eq_true_iff
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (site : IndexedCardinalitySite definitions nodeCount) :
    indexedMaximumSiteBool definitions state site = true ↔
      (definitions.get site.1).kind = .maximum ∧
      state.base.closedLabel site.2 (.pos (definitions.get site.1).marker) ∧
      (definitions.get site.1).bound + 1 ≤
        (rustMaximumRepresentatives state (definitions.get site.1) site.2).length := by
  exact rustMaximumSiteBool_eq_true_iff state (definitions.get site.1, site.2)

noncomputable def selectIndexedViolatingMaximum
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role) :
    Option (IndexedCardinalitySite definitions nodeCount) :=
  firstMatch (indexedMaximumSiteBool definitions state)
    (allIndexedCardinalitySites definitions nodeCount)

theorem selectIndexedViolatingMaximum_eq_none_iff
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role) :
    selectIndexedViolatingMaximum definitions state = none ↔
      ∀ site, indexedMaximumSiteBool definitions state site = false := by
  rw [selectIndexedViolatingMaximum, firstMatch_eq_none_iff]
  constructor
  · intro hscan site
    exact hscan site mem_allIndexedCardinalitySites
  · intro hscan site _
    exact hscan site

theorem selectIndexedViolatingMaximum_closedRefutes
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedViolatingMaximum definitions state = some site)
    (hwidth : (definitions.get site.1).bound + 1 ≤
      (rustMaximumRepresentatives state (definitions.get site.1) site.2).length)
    (children : ∀ left right : Fin ((definitions.get site.1).bound + 1), left ≠ right →
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
        (state.merge
          (rustPrefixVector
            (rustMaximumRepresentatives state (definitions.get site.1) site.2)
            ((definitions.get site.1).bound + 1) hwidth left)
          (rustPrefixVector
            (rustMaximumRepresentatives state (definitions.get site.1) site.2)
            ((definitions.get site.1).bound + 1) hwidth right))) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectIndexedViolatingMaximum] using hselect)
  have hproperties :=
    (indexedMaximumSiteBool_eq_true_iff definitions state site).mp hfound.2
  exact .maximum state (definitions.get site.1) (List.get_mem definitions site.1)
    hproperties.1 site.2 hproperties.2.1
    (rustPrefixVector (rustMaximumRepresentatives state (definitions.get site.1) site.2)
      ((definitions.get site.1).bound + 1) hwidth)
    (fun index => (rustMaximumPrefixVector_qualifies state (definitions.get site.1) site.2
      hwidth index).1)
    (fun index => (rustMaximumPrefixVector_qualifies state (definitions.get site.1) site.2
      hwidth index).2)
    children

theorem selectIndexedViolatingMaximum_source_lt_active
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (active : Nat) (hprefix : state.InactivePrefixFresh active)
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedViolatingMaximum definitions state = some site) :
    site.2.1 < active := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectIndexedViolatingMaximum] using hselect)
  have hproperties :=
    (indexedMaximumSiteBool_eq_true_iff definitions state site).mp hfound.2
  exact state.lt_active_of_closedLabel active hprefix site.2
    (.pos (definitions.get site.1).marker) hproperties.2.1

/-- One selected production-shaped cardinality obstruction.  Immediate clashes
have no recursive children; the other constructors expose exactly the child
family required by the corresponding quotient-closed refutation rule. -/
inductive CardinalityProductionStep
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount))
    (active : Nat) : Type where
  | equalityApart
      (candidate : EqualityApartCandidate (Fin nodeCount))
      (hselect : selectEqualityApartClash state = some candidate)
  | conceptClash
      (hnoApart : selectEqualityApartClash state = none)
      (candidate : EqClashCandidate (Fin nodeCount) Concept)
      (hselect : selectCardinalityConceptClash state = some candidate)
  | branch
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (grounding : Grounding Variable (Fin nodeCount) Concept Role)
      (hselect : selectCardinalityClauseGrounding ontology state = some grounding)
  | witness
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectCardinalityClauseGrounding ontology state = none)
      (candidate : WitnessCandidate (Fin nodeCount) Concept Role)
      (hselect : selectEqUnblockedUnwitnessed state.base parent ancestors = some candidate)
      (hfit : active < nodeCount)
      (hprefix : state.InactivePrefixFresh active)
  | minimum
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectCardinalityClauseGrounding ontology state = none)
      (hnoWitness : selectEqUnblockedUnwitnessed state.base parent ancestors = none)
      (site : IndexedCardinalitySite definitions nodeCount)
      (hselect : selectIndexedExpandableMinimum definitions state parent ancestors expanded =
        some site)
      (hfit : active + (definitions.get site.1).bound ≤ nodeCount)
      (hprefix : state.InactivePrefixFresh active)
  | maximum
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectCardinalityClauseGrounding ontology state = none)
      (hnoWitness : selectEqUnblockedUnwitnessed state.base parent ancestors = none)
      (hnoMinimum : selectIndexedExpandableMinimum definitions state parent ancestors expanded =
        none)
      (site : IndexedCardinalitySite definitions nodeCount)
      (hselect : selectIndexedViolatingMaximum definitions state = some site)
      (hwidth : (definitions.get site.1).bound + 1 ≤
        (rustMaximumRepresentatives state (definitions.get site.1) site.2).length)
      (hprefix : state.InactivePrefixFresh active)

/-- Every recursive child selected by a production step is closed. -/
def CardinalityProductionStep.ChildrenClosed
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {state : DistinctEqState (Fin nodeCount) Concept Role}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)}
    {expanded : Finset (IndexedCardinalitySite definitions nodeCount)}
    {active : Nat}
    (step : CardinalityProductionStep ontology definitions state parent ancestors expanded
      active) : Prop :=
  match step with
  | .equalityApart _ _ => True
  | .conceptClash _ _ _ => True
  | .branch _ _ grounding _ =>
      ∀ atom, atom ∈ grounding.1.head →
        ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
          (state.assertAtom grounding.2 atom)
  | .witness _ _ _ candidate _ hfit _ =>
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
        (state.materializeWitness candidate.2.2
          (rustNextTarget active nodeCount hfit) candidate.1 candidate.2.1)
  | .minimum _ _ _ _ site _ hfit _ =>
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
        (state.materializeMinimum site.2
          (rustConsecutiveTargets active (definitions.get site.1).bound nodeCount hfit)
          (definitions.get site.1).role (definitions.get site.1).filler)
  | .maximum _ _ _ _ _ site _ hwidth _ =>
      ∀ left right : Fin ((definitions.get site.1).bound + 1), left ≠ right →
        ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
          (state.merge
            (rustPrefixVector
              (rustMaximumRepresentatives state (definitions.get site.1) site.2)
              ((definitions.get site.1).bound + 1) hwidth left)
            (rustPrefixVector
              (rustMaximumRepresentatives state (definitions.get site.1) site.2)
              ((definitions.get site.1).bound + 1) hwidth right))

/-- Closing every recursive child of the selected first obstruction closes the
parent state.  Earlier-selector exhaustion fields are operational evidence;
soundness itself follows from the selected rule. -/
theorem CardinalityProductionStep.closedRefutes_of_children
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {state : DistinctEqState (Fin nodeCount) Concept Role}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)}
    {expanded : Finset (IndexedCardinalitySite definitions nodeCount)}
    {active : Nat}
    (step : CardinalityProductionStep ontology definitions state parent ancestors expanded
      active)
    (hchildren : step.ChildrenClosed) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state := by
  cases step with
  | equalityApart candidate hselect =>
      exact (selectEqualityApartClash_refutes ontology definitions state hselect).toClosed
  | conceptClash hnoApart candidate hselect =>
      exact (selectCardinalityConceptClash_refutes ontology definitions state hselect).toClosed
  | branch hnoApart hnoClash grounding hselect =>
      exact selectCardinalityClauseGrounding_closedRefutes ontology definitions state
        hselect hchildren
  | witness hnoApart hnoClash hnoClause candidate hselect hfit hprefix =>
      classical
      have hcandidate := firstMatch_eq_some_mem
        (by simpa [selectEqUnblockedUnwitnessed] using hselect)
      have hproperties :=
        (eqUnblockedWitnessCandidateBool_eq_true_iff state.base parent ancestors
          candidate).mp hcandidate.2
      exact .witness state candidate.2.2 (rustNextTarget active nodeCount hfit)
        candidate.1 candidate.2.1 hproperties.1
        (hprefix (rustNextTarget active nodeCount hfit) (by simp [rustNextTarget]))
        hchildren
  | minimum hnoApart hnoClash hnoClause hnoWitness site hselect hfit hprefix =>
      exact selectIndexedExpandableMinimum_closedRefutes ontology definitions state
        parent ancestors expanded hselect active hprefix hfit hchildren
  | maximum hnoApart hnoClash hnoClause hnoWitness hnoMinimum site hselect hwidth hprefix =>
      exact selectIndexedViolatingMaximum_closedRefutes ontology definitions state hselect
        hwidth hchildren

#print axioms CardinalityProductionStep.closedRefutes_of_children
#print axioms selectIndexedExpandableMinimum_eq_none_iff
#print axioms selectIndexedExpandableMinimum_closedRefutes
#print axioms selectIndexedExpandableMinimum_source_lt_active
#print axioms selectIndexedViolatingMaximum_eq_none_iff
#print axioms selectIndexedViolatingMaximum_closedRefutes
#print axioms selectIndexedViolatingMaximum_source_lt_active

end ContextCalculus.Hypertableau
