import ContextCalculus.HypertableauCardinalityRuntimeSearch
import ContextCalculus.HypertableauCardinalityBlockedSearch

/-!
# Production-shaped cardinality hypertableau expansion

This module packages the six cardinality runtime controls into one typed
first-obstruction layer.  Each recursive constructor carries the exact selected
site and the earlier-selector exhaustion facts that establish production
priority.  Witness and minimum allocation use Rust's active-prefix IDs;
maximum expansion uses the deterministic greedy prefix vector.
-/

namespace ContextCalculus.Hypertableau

def liftActiveAssignment (hfit : active ≤ nodeCount)
    (assignment : Variable → Fin active) : Variable → Fin nodeCount :=
  fun variableId => ⟨(assignment variableId).1,
    lt_of_lt_of_le (assignment variableId).2 hfit⟩

/-- Clause groundings restricted to Rust's active node prefix. -/
noncomputable def allActiveGroundings
    [Fintype Variable] [DecidableEq Variable]
    (ontology : List (Clause Variable Concept Role))
    (active nodeCount : Nat) (hfit : active ≤ nodeCount) :
    List (Grounding Variable (Fin nodeCount) Concept Role) := by
  classical
  exact ontology.flatMap fun clause =>
    (Finset.univ.toList : List (Variable → Fin active)).map fun assignment =>
      (clause, liftActiveAssignment hfit assignment)

theorem mem_allActiveGroundings_properties
    [Fintype Variable] [DecidableEq Variable]
    (ontology : List (Clause Variable Concept Role))
    (active nodeCount : Nat) (hfit : active ≤ nodeCount)
    {grounding : Grounding Variable (Fin nodeCount) Concept Role}
    (hmem : grounding ∈ allActiveGroundings ontology active nodeCount hfit) :
    grounding.1 ∈ ontology ∧ AssignmentWithinActive grounding.2 active := by
  classical
  rcases List.mem_flatMap.mp hmem with ⟨clause, hclause, hgrounding⟩
  rcases List.mem_map.mp hgrounding with ⟨assignment, _, heq⟩
  rw [← heq]
  exact ⟨hclause, fun variableId => (assignment variableId).2⟩

noncomputable def selectActiveCardinalityClauseGrounding
    [Fintype Variable] [DecidableEq Variable]
    (ontology : List (Clause Variable Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (active : Nat) (hfit : active ≤ nodeCount) :
    Option (Grounding Variable (Fin nodeCount) Concept Role) :=
  firstMatch (eqGroundingUndischarged state.base)
    (allActiveGroundings ontology active nodeCount hfit)

theorem selectActiveCardinalityClauseGrounding_properties
    [Fintype Variable] [DecidableEq Variable]
    (ontology : List (Clause Variable Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (active : Nat) (hfit : active ≤ nodeCount)
    {grounding : Grounding Variable (Fin nodeCount) Concept Role}
    (hselect : selectActiveCardinalityClauseGrounding ontology state active hfit =
      some grounding) :
    grounding.1 ∈ ontology ∧ AssignmentWithinActive grounding.2 active ∧
      (∀ atom ∈ grounding.1.body, state.base.closedHoldsAtom grounding.2 atom) ∧
      (∀ atom ∈ grounding.1.head, ¬state.base.closedHoldsAtom grounding.2 atom) := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectActiveCardinalityClauseGrounding] using hselect)
  have hmem := mem_allActiveGroundings_properties ontology active nodeCount hfit hfound.1
  have hgrounding := eqGroundingUndischarged_eq_true_iff.mp hfound.2
  exact ⟨hmem.1, hmem.2, hgrounding.1, hgrounding.2⟩

theorem selectActiveCardinalityClauseGrounding_closedRefutes
    [Fintype Variable] [DecidableEq Variable]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (active : Nat) (hfit : active ≤ nodeCount)
    {grounding : Grounding Variable (Fin nodeCount) Concept Role}
    (hselect : selectActiveCardinalityClauseGrounding ontology state active hfit =
      some grounding)
    (children : ∀ atom, atom ∈ grounding.1.head →
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions
        (state.assertAtom grounding.2 atom)) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state := by
  have hproperties := selectActiveCardinalityClauseGrounding_properties ontology state active
    hfit hselect
  exact .branch state grounding.1 hproperties.1 grounding.2 hproperties.2.2.1 children

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

theorem selectIndexedExpandableMinimum_not_expanded
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role))
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (expanded : Finset (IndexedCardinalitySite definitions nodeCount))
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedExpandableMinimum definitions state parent ancestors expanded =
      some site) : site ∉ expanded := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectIndexedExpandableMinimum] using hselect)
  have hproperties := (indexedMinimumSiteBool_eq_true_iff definitions state parent ancestors
    expanded site).mp hfound.2
  intro hmem
  exact hproperties.2.2.1 ⟨site.2, hmem, state.base.equiv_equivalence.1 site.2⟩

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

/-- The branch-local data mutated by Rust's distinct-cardinality recursion.
Parent/address arrays determine blocking and wire output, while this logical
projection contains exactly the fields used by the termination assertion. -/
structure CardinalityRuntimeConfig
    (Concept Role : Type) (definitions : List (CardinalityDef Concept Role))
    (nodeCount : Nat) where
  state : DistinctEqState (Fin nodeCount) Concept Role
  active : Nat
  expanded : Finset (IndexedCardinalitySite definitions nodeCount)
  active_le : active ≤ nodeCount
  inactive_fresh : state.InactivePrefixFresh active

abbrev CardinalityProgressFact
    (definitions : List (CardinalityDef Concept Role)) (nodeCount : Nat)
    (Concept Role : Type) :=
  EqGuardedFact (Fin nodeCount) Concept Role ⊕
    ((Fin nodeCount × Fin nodeCount) ⊕ IndexedCardinalitySite definitions nodeCount)

noncomputable def DistinctEqState.apartFacts
    [Fintype Node] [DecidableEq Node]
    (state : DistinctEqState Node Concept Role) : Finset (Node × Node) := by
  classical
  exact Finset.univ.filter fun pair => state.apart pair.1 pair.2

@[simp] theorem DistinctEqState.mem_apartFacts
    [Fintype Node] [DecidableEq Node]
    (state : DistinctEqState Node Concept Role) (pair : Node × Node) :
    pair ∈ state.apartFacts ↔ state.apart pair.1 pair.2 := by
  classical
  simp [DistinctEqState.apartFacts]

/-- Lean's extensional counterpart of Rust's release-mode
`progress_measure`: guarded labels/edges/obligations/equalities, directed apart
pairs, and expanded minimum IDs. -/
noncomputable def CardinalityRuntimeConfig.progressFacts
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount) :
    Finset (CardinalityProgressFact definitions nodeCount Concept Role) := by
  classical
  exact Finset.univ.filter fun fact =>
    match fact with
    | .inl guarded => config.state.base.holdsEqGuardedFact guarded
    | .inr (.inl pair) => config.state.apart pair.1 pair.2
    | .inr (.inr site) => site ∈ config.expanded

@[simp] theorem CardinalityRuntimeConfig.mem_progressFacts
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (fact : CardinalityProgressFact definitions nodeCount Concept Role) :
    fact ∈ config.progressFacts ↔
      match fact with
      | .inl guarded => config.state.base.holdsEqGuardedFact guarded
      | .inr (.inl pair) => config.state.apart pair.1 pair.2
      | .inr (.inr site) => site ∈ config.expanded := by
  classical
  simp [CardinalityRuntimeConfig.progressFacts]

theorem EqState.eqGuardedFacts_materializeMinimum_subset
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (source : Node)
    (targets : Fin count → Node) (role : Role) (filler : Concept) :
    state.eqGuardedFacts ⊆
      (state.materializeMinimum source targets role filler).eqGuardedFacts := by
  classical
  intro fact hfact
  simp only [EqState.mem_eqGuardedFacts] at hfact ⊢
  rcases fact with fact | ⟨left, right⟩
  · rcases fact with label | fact
    · exact Or.inl hfact
    · rcases fact with edge | obligation
      · exact Or.inl hfact
      · exact hfact
  · exact hfact

def CardinalityRuntimeConfig.minimumChild
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedExpandableMinimum definitions config.state parent ancestors
      config.expanded = some site)
    (hfit : config.active + (definitions.get site.1).bound ≤ nodeCount) :
    CardinalityRuntimeConfig Concept Role definitions nodeCount where
  state := config.state.materializeMinimum site.2
    (rustConsecutiveTargets config.active (definitions.get site.1).bound nodeCount hfit)
    (definitions.get site.1).role (definitions.get site.1).filler
  active := config.active + (definitions.get site.1).bound
  expanded := insert site config.expanded
  active_le := hfit
  inactive_fresh := config.state.inactivePrefixFresh_materializeMinimum config.active
    (definitions.get site.1).bound config.inactive_fresh site.2
    (selectIndexedExpandableMinimum_source_lt_active definitions config.state parent ancestors
      config.expanded config.active config.inactive_fresh hselect)
    (definitions.get site.1).role (definitions.get site.1).filler hfit

theorem CardinalityRuntimeConfig.minimumChild_progress
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedExpandableMinimum definitions config.state parent ancestors
      config.expanded = some site)
    (hfit : config.active + (definitions.get site.1).bound ≤ nodeCount) :
    config.progressFacts ⊂
      (config.minimumChild parent ancestors hselect hfit).progressFacts := by
  classical
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro fact hfact
    simp only [CardinalityRuntimeConfig.mem_progressFacts] at hfact ⊢
    rcases fact with guarded | fact
    · have hpreserved := EqState.eqGuardedFacts_materializeMinimum_subset config.state.base site.2
        (rustConsecutiveTargets config.active (definitions.get site.1).bound nodeCount hfit)
        (definitions.get site.1).role (definitions.get site.1).filler
        (by simpa only [EqState.mem_eqGuardedFacts] using hfact)
      simpa only [EqState.mem_eqGuardedFacts] using hpreserved
    · rcases fact with pair | expandedSite
      · exact Or.inl hfact
      · exact Finset.mem_insert_of_mem hfact
  · intro hequal
    have hnew : (Sum.inr (Sum.inr site) :
        CardinalityProgressFact definitions nodeCount Concept Role) ∈
        (config.minimumChild parent ancestors hselect hfit).progressFacts := by
      simp [CardinalityRuntimeConfig.minimumChild]
    rw [← hequal] at hnew
    exact (selectIndexedExpandableMinimum_not_expanded definitions config.state parent ancestors
      config.expanded hselect) (by simpa using hnew)

def CardinalityRuntimeConfig.clauseChild
    [Fintype Variable] [DecidableEq Variable]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (ontology : List (Clause Variable Concept Role))
    {grounding : Grounding Variable (Fin nodeCount) Concept Role}
    (hselect : selectActiveCardinalityClauseGrounding ontology config.state config.active
      config.active_le = some grounding)
    (atom : Atom Variable Concept Role) :
    CardinalityRuntimeConfig Concept Role definitions nodeCount where
  state := config.state.assertAtom grounding.2 atom
  active := config.active
  expanded := config.expanded
  active_le := config.active_le
  inactive_fresh := config.state.inactivePrefixFresh_assertAtom config.active
    config.inactive_fresh grounding.2
    (selectActiveCardinalityClauseGrounding_properties ontology config.state config.active
      config.active_le hselect).2.1 atom

theorem CardinalityRuntimeConfig.clauseChild_progress
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (ontology : List (Clause Variable Concept Role))
    {grounding : Grounding Variable (Fin nodeCount) Concept Role}
    (hselect : selectActiveCardinalityClauseGrounding ontology config.state config.active
      config.active_le = some grounding)
    (atom : Atom Variable Concept Role) (hatom : atom ∈ grounding.1.head) :
    config.progressFacts ⊂ (config.clauseChild ontology hselect atom).progressFacts := by
  classical
  have hproperties := selectActiveCardinalityClauseGrounding_properties ontology config.state
    config.active config.active_le hselect
  have hgrowth := config.state.base.eqGuardedFacts_assertAtom_ssubset grounding.2 atom
    (hproperties.2.2.2 atom hatom)
  rw [Finset.ssubset_iff_subset_ne] at hgrowth ⊢
  constructor
  · intro fact hfact
    simp only [CardinalityRuntimeConfig.mem_progressFacts] at hfact ⊢
    rcases fact with guarded | fact
    · have hpreserved := hgrowth.1
        (by simpa only [EqState.mem_eqGuardedFacts] using hfact)
      simpa only [EqState.mem_eqGuardedFacts] using hpreserved
    · rcases fact with pair | site
      · exact hfact
      · exact hfact
  · intro hequal
    apply hgrowth.2
    ext guarded
    constructor
    · intro hparent
      have hlift : (Sum.inl guarded :
          CardinalityProgressFact definitions nodeCount Concept Role) ∈
          config.progressFacts := by
        simpa only [CardinalityRuntimeConfig.mem_progressFacts,
          EqState.mem_eqGuardedFacts] using hparent
      rw [hequal] at hlift
      simpa only [CardinalityRuntimeConfig.mem_progressFacts,
        EqState.mem_eqGuardedFacts] using hlift
    · intro hchild
      have hlift : (Sum.inl guarded :
          CardinalityProgressFact definitions nodeCount Concept Role) ∈
          (config.clauseChild ontology hselect atom).progressFacts := by
        simpa only [CardinalityRuntimeConfig.mem_progressFacts,
          EqState.mem_eqGuardedFacts] using hchild
      rw [← hequal] at hlift
      simpa only [CardinalityRuntimeConfig.mem_progressFacts,
        EqState.mem_eqGuardedFacts] using hlift

theorem DistinctEqState.lt_active_of_obligation
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (active : Nat) (hprefix : state.InactivePrefixFresh active)
    (source : Fin nodeCount) (role : Role) (filler : Lit Concept)
    (hobligation : state.base.base.obligation role filler source) : source.1 < active := by
  by_contra hnot
  exact (hprefix source (Nat.le_of_not_gt hnot)).1.1.2.2 role filler hobligation

theorem selectCardinalityWitness_source_lt_active
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (active : Nat) (hprefix : state.InactivePrefixFresh active)
    {candidate : WitnessCandidate (Fin nodeCount) Concept Role}
    (hselect : selectEqUnblockedUnwitnessed state.base parent ancestors = some candidate) :
    candidate.2.2.1 < active := by
  classical
  have hfound := firstMatch_eq_some_mem
    (by simpa [selectEqUnblockedUnwitnessed] using hselect)
  have hproperties :=
    (eqUnblockedWitnessCandidateBool_eq_true_iff state.base parent ancestors candidate).mp
      hfound.2
  exact state.lt_active_of_obligation active hprefix candidate.2.2 candidate.1
    candidate.2.1 hproperties.1

def CardinalityRuntimeConfig.witnessChild
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    {candidate : WitnessCandidate (Fin nodeCount) Concept Role}
    (hselect : selectEqUnblockedUnwitnessed config.state.base parent ancestors = some candidate)
    (hfit : config.active < nodeCount) :
    CardinalityRuntimeConfig Concept Role definitions nodeCount where
  state := config.state.materializeWitness candidate.2.2
    (rustNextTarget config.active nodeCount hfit) candidate.1 candidate.2.1
  active := config.active + 1
  expanded := config.expanded
  active_le := hfit
  inactive_fresh := config.state.inactivePrefixFresh_materializeWitness config.active
    config.inactive_fresh candidate.2.2
    (selectCardinalityWitness_source_lt_active config.state parent ancestors config.active
      config.inactive_fresh hselect) candidate.1 candidate.2.1 hfit

theorem CardinalityRuntimeConfig.witnessChild_progress
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    {candidate : WitnessCandidate (Fin nodeCount) Concept Role}
    (hselect : selectEqUnblockedUnwitnessed config.state.base parent ancestors = some candidate)
    (hfit : config.active < nodeCount) :
    config.progressFacts ⊂
      (config.witnessChild parent ancestors hselect hfit).progressFacts := by
  classical
  have hfresh := config.inactive_fresh (rustNextTarget config.active nodeCount hfit)
    (by simp [rustNextTarget])
  have hgrowth := config.state.base.eqGuardedFacts_materializeWitness_ssubset
    candidate.2.2 (rustNextTarget config.active nodeCount hfit) candidate.1 candidate.2.1
    hfresh.1
  rw [Finset.ssubset_iff_subset_ne] at hgrowth ⊢
  constructor
  · intro fact hfact
    simp only [CardinalityRuntimeConfig.mem_progressFacts] at hfact ⊢
    rcases fact with guarded | fact
    · have hpreserved := hgrowth.1
        (by simpa only [EqState.mem_eqGuardedFacts] using hfact)
      simpa only [EqState.mem_eqGuardedFacts] using hpreserved
    · rcases fact with pair | site <;> exact hfact
  · intro hequal
    apply hgrowth.2
    ext guarded
    constructor
    · intro hparent
      have hlift : (Sum.inl guarded :
          CardinalityProgressFact definitions nodeCount Concept Role) ∈
          config.progressFacts := by
        simpa only [CardinalityRuntimeConfig.mem_progressFacts,
          EqState.mem_eqGuardedFacts] using hparent
      rw [hequal] at hlift
      simpa only [CardinalityRuntimeConfig.mem_progressFacts,
        EqState.mem_eqGuardedFacts] using hlift

    · intro hchild
      have hlift : (Sum.inl guarded :
          CardinalityProgressFact definitions nodeCount Concept Role) ∈
          (config.witnessChild parent ancestors hselect hfit).progressFacts := by
        simpa only [CardinalityRuntimeConfig.mem_progressFacts,
          EqState.mem_eqGuardedFacts] using hchild
      rw [← hequal] at hlift
      simpa only [CardinalityRuntimeConfig.mem_progressFacts,
        EqState.mem_eqGuardedFacts] using hlift

theorem rustMaximumPrefixVector_lt_active
    (state : DistinctEqState (Fin nodeCount) Concept Role)
    (active : Nat) (hprefix : state.InactivePrefixFresh active)
    (definition : CardinalityDef Concept Role) (source : Fin nodeCount)
    (hwidth : definition.bound + 1 ≤
      (rustMaximumRepresentatives state definition source).length)
    (index : Fin (definition.bound + 1)) :
    (rustPrefixVector (rustMaximumRepresentatives state definition source)
      (definition.bound + 1) hwidth index).1 < active := by
  have hfiller := (rustMaximumPrefixVector_qualifies state definition source
    hwidth index).2
  exact state.lt_active_of_closedLabel active hprefix _ (.pos definition.filler) hfiller

theorem EqState.eqGuardedFacts_merge_ssubset
    [Fintype Node] [DecidableEq Node]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (state : EqState Node Concept Role) (left right : Node)
    (hdistinct : ¬state.equiv left right) :
    state.eqGuardedFacts ⊂ (state.merge left right).eqGuardedFacts := by
  classical
  let assignment : Bool → Node := fun side => if side then right else left
  have habsent : ¬state.closedHoldsAtom assignment (.eq false true) := by
    simpa [EqState.closedHoldsAtom, assignment] using hdistinct
  simpa [EqState.assertAtom, assignment] using
    (state.eqGuardedFacts_assertAtom_ssubset assignment (.eq false true) habsent)

noncomputable def CardinalityRuntimeConfig.maximumChild
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    {site : IndexedCardinalitySite definitions nodeCount}
    (_hselect : selectIndexedViolatingMaximum definitions config.state = some site)
    (hwidth : (definitions.get site.1).bound + 1 ≤
      (rustMaximumRepresentatives config.state (definitions.get site.1) site.2).length)
    (left right : Fin ((definitions.get site.1).bound + 1)) (_hne : left ≠ right) :
    CardinalityRuntimeConfig Concept Role definitions nodeCount where
  state := config.state.merge
    (rustPrefixVector
      (rustMaximumRepresentatives config.state (definitions.get site.1) site.2)
      ((definitions.get site.1).bound + 1) hwidth left)
    (rustPrefixVector
      (rustMaximumRepresentatives config.state (definitions.get site.1) site.2)
      ((definitions.get site.1).bound + 1) hwidth right)
  active := config.active
  expanded := config.expanded
  active_le := config.active_le
  inactive_fresh := config.state.inactivePrefixFresh_merge config.active
    config.inactive_fresh _ _
    (rustMaximumPrefixVector_lt_active config.state config.active config.inactive_fresh
      (definitions.get site.1) site.2 hwidth left)
    (rustMaximumPrefixVector_lt_active config.state config.active config.inactive_fresh
      (definitions.get site.1) site.2 hwidth right)

theorem CardinalityRuntimeConfig.maximumChild_progress
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedViolatingMaximum definitions config.state = some site)
    (hwidth : (definitions.get site.1).bound + 1 ≤
      (rustMaximumRepresentatives config.state (definitions.get site.1) site.2).length)
    (left right : Fin ((definitions.get site.1).bound + 1)) (hne : left ≠ right) :
    config.progressFacts ⊂
      (config.maximumChild hselect hwidth left right hne).progressFacts := by
  classical
  let witnesses := rustPrefixVector
    (rustMaximumRepresentatives config.state (definitions.get site.1) site.2)
    ((definitions.get site.1).bound + 1) hwidth
  have hdistinct : ¬config.state.base.equiv (witnesses left) (witnesses right) :=
    rustMaximumPrefixVector_pairwise config.state (definitions.get site.1) site.2
      hwidth left right hne
  have hgrowth := config.state.base.eqGuardedFacts_merge_ssubset
    (witnesses left) (witnesses right) hdistinct
  rw [Finset.ssubset_iff_subset_ne] at hgrowth ⊢
  constructor
  · intro fact hfact
    simp only [CardinalityRuntimeConfig.mem_progressFacts] at hfact ⊢
    rcases fact with guarded | fact
    · have hpreserved := hgrowth.1
        (by simpa only [EqState.mem_eqGuardedFacts] using hfact)
      simpa only [EqState.mem_eqGuardedFacts, witnesses] using hpreserved
    · rcases fact with pair | expandedSite <;> exact hfact
  · intro hequal
    apply hgrowth.2
    ext guarded
    constructor
    · intro hparent
      have hlift : (Sum.inl guarded :
          CardinalityProgressFact definitions nodeCount Concept Role) ∈
          config.progressFacts := by
        simpa only [CardinalityRuntimeConfig.mem_progressFacts,
          EqState.mem_eqGuardedFacts] using hparent
      rw [hequal] at hlift
      simpa only [CardinalityRuntimeConfig.mem_progressFacts,
        EqState.mem_eqGuardedFacts, witnesses] using hlift
    · intro hchild
      have hlift : (Sum.inl guarded :
          CardinalityProgressFact definitions nodeCount Concept Role) ∈
          (config.maximumChild hselect hwidth left right hne).progressFacts := by
        simpa only [CardinalityRuntimeConfig.mem_progressFacts,
          EqState.mem_eqGuardedFacts, witnesses] using hchild
      rw [← hequal] at hlift
      simpa only [CardinalityRuntimeConfig.mem_progressFacts,
        EqState.mem_eqGuardedFacts] using hlift
def CardinalityStrictGrowth
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (child parent : CardinalityRuntimeConfig Concept Role definitions nodeCount) : Prop :=
  parent.progressFacts ⊂ child.progressFacts

theorem cardinalityStrictGrowth_wellFounded
    (Concept Role : Type)
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (definitions : List (CardinalityDef Concept Role)) (nodeCount : Nat) :
    WellFounded (@CardinalityStrictGrowth Concept Role definitions nodeCount _ _ _ _) := by
  classical
  exact InvImage.wf CardinalityRuntimeConfig.progressFacts
    (strictGrowth_wellFounded
      (CardinalityProgressFact definitions nodeCount Concept Role))

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
    (active : Nat) (activeFit : active ≤ nodeCount) : Type where
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
      (hselect : selectActiveCardinalityClauseGrounding ontology state active activeFit =
        some grounding)
  | witness
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectActiveCardinalityClauseGrounding ontology state active activeFit = none)
      (candidate : WitnessCandidate (Fin nodeCount) Concept Role)
      (hselect : selectEqUnblockedUnwitnessed state.base parent ancestors = some candidate)
      (hfit : active < nodeCount)
      (hprefix : state.InactivePrefixFresh active)
  | minimum
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectActiveCardinalityClauseGrounding ontology state active activeFit = none)
      (hnoWitness : selectEqUnblockedUnwitnessed state.base parent ancestors = none)
      (site : IndexedCardinalitySite definitions nodeCount)
      (hselect : selectIndexedExpandableMinimum definitions state parent ancestors expanded =
        some site)
      (hfit : active + (definitions.get site.1).bound ≤ nodeCount)
      (hprefix : state.InactivePrefixFresh active)
  | maximum
      (hnoApart : selectEqualityApartClash state = none)
      (hnoClash : selectCardinalityConceptClash state = none)
      (hnoClause : selectActiveCardinalityClauseGrounding ontology state active activeFit = none)
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
    {active : Nat} {activeFit : active ≤ nodeCount}
    (step : CardinalityProductionStep ontology definitions state parent ancestors expanded
      active activeFit) : Prop :=
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
    {active : Nat} {activeFit : active ≤ nodeCount}
    (step : CardinalityProductionStep ontology definitions state parent ancestors expanded
      active activeFit)
    (hchildren : step.ChildrenClosed) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions state := by
  cases step with
  | equalityApart candidate hselect =>
      exact (selectEqualityApartClash_refutes ontology definitions state hselect).toClosed
  | conceptClash hnoApart candidate hselect =>
      exact (selectCardinalityConceptClash_refutes ontology definitions state hselect).toClosed
  | branch hnoApart hnoClash grounding hselect =>
      exact selectActiveCardinalityClauseGrounding_closedRefutes ontology definitions state
        active activeFit hselect hchildren
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

/-- Exact recursive child configurations exposed by one selected production
obstruction. Immediate clashes have no children. -/
def CardinalityProductionStep.ChildConfig
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (step : CardinalityProductionStep ontology definitions config.state parent ancestors
      config.expanded config.active config.active_le)
    (child : CardinalityRuntimeConfig Concept Role definitions nodeCount) : Prop :=
  match step with
  | .equalityApart _ _ => False
  | .conceptClash _ _ _ => False
  | .branch _ _ grounding hselect =>
      ∃ atom, ∃ hatom : atom ∈ grounding.1.head,
        child = config.clauseChild ontology hselect atom
  | .witness _ _ _ candidate hselect hfit _ =>
      child = config.witnessChild parent ancestors hselect hfit
  | .minimum _ _ _ _ site hselect hfit _ =>
      child = config.minimumChild parent ancestors hselect hfit
  | .maximum _ _ _ _ _ site hselect hwidth _ =>
      ∃ left right, ∃ hne : left ≠ right,
        child = config.maximumChild hselect hwidth left right hne

theorem CardinalityProductionStep.child_strictGrowth
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {config child : CardinalityRuntimeConfig Concept Role definitions nodeCount}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)}
    (step : CardinalityProductionStep ontology definitions config.state parent ancestors
      config.expanded config.active config.active_le)
    (hchild : step.ChildConfig config parent ancestors child) :
    CardinalityStrictGrowth child config := by
  cases step with
  | equalityApart candidate hselect => exact hchild.elim
  | conceptClash hnoApart candidate hselect => exact hchild.elim
  | branch hnoApart hnoClash grounding hselect =>
      rcases hchild with ⟨atom, hatom, rfl⟩
      exact config.clauseChild_progress ontology hselect atom hatom
  | witness hnoApart hnoClash hnoClause candidate hselect hfit hprefix =>
      subst child
      exact config.witnessChild_progress parent ancestors hselect hfit
  | minimum hnoApart hnoClash hnoClause hnoWitness site hselect hfit hprefix =>
      subst child
      exact config.minimumChild_progress parent ancestors hselect hfit
  | maximum hnoApart hnoClash hnoClause hnoWitness hnoMinimum site hselect hwidth hprefix =>
      rcases hchild with ⟨left, right, hne, rfl⟩
      exact config.maximumChild_progress hselect hwidth left right hne

theorem CardinalityProductionStep.closedRefutes_of_childConfigs
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (step : CardinalityProductionStep ontology definitions config.state parent ancestors
      config.expanded config.active config.active_le)
    (hchildren : ∀ child, step.ChildConfig config parent ancestors child →
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions child.state) :
    ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions config.state := by
  apply step.closedRefutes_of_children
  cases step with
  | equalityApart candidate hselect => trivial
  | conceptClash hnoApart candidate hselect => trivial
  | branch hnoApart hnoClash grounding hselect =>
      intro atom hatom
      simpa [CardinalityRuntimeConfig.clauseChild] using
        hchildren (config.clauseChild ontology hselect atom) ⟨atom, hatom, rfl⟩
  | witness hnoApart hnoClash hnoClause candidate hselect hfit hprefix =>
      simpa [CardinalityRuntimeConfig.witnessChild] using
        hchildren (config.witnessChild parent ancestors hselect hfit) rfl
  | minimum hnoApart hnoClash hnoClause hnoWitness site hselect hfit hprefix =>
      simpa [CardinalityRuntimeConfig.minimumChild] using
        hchildren (config.minimumChild parent ancestors hselect hfit) rfl
  | maximum hnoApart hnoClash hnoClause hnoWitness hnoMinimum site hselect hwidth hprefix =>
      intro left right hne
      simpa [CardinalityRuntimeConfig.maximumChild] using
        hchildren (config.maximumChild hselect hwidth left right hne)
          ⟨left, right, hne, rfl⟩

/-- Well-founded induction principle for the exact production child relation.
It is the recursion kernel used to construct total finite-budget outcomes. -/
theorem cardinalityProduction_induction
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (nodeCount : Nat)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (P : CardinalityRuntimeConfig Concept Role definitions nodeCount → Prop)
    (hstep : ∀ config,
      (∀ (step : CardinalityProductionStep ontology definitions config.state parent ancestors
          config.expanded config.active config.active_le) child,
        step.ChildConfig config parent ancestors child → P child) → P config) :
    ∀ config, P config := by
  intro root
  induction root using
      (cardinalityStrictGrowth_wellFounded Concept Role definitions nodeCount).induction with
  | h config ih =>
      apply hstep config
      intro step child hchild
      exact ih child (step.child_strictGrowth hchild)

/-- Total result of Rust's first-obstruction control at one finite-budget
configuration. A selected witness or minimum that does not fit is an explicit
frontier, not a terminal model. -/
inductive CardinalityControlOutcome
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount)) : Type where
  | step
      (selected : CardinalityProductionStep ontology definitions config.state parent ancestors
        config.expanded config.active config.active_le)
  | witnessFrontier
      (hnoApart : selectEqualityApartClash config.state = none)
      (hnoClash : selectCardinalityConceptClash config.state = none)
      (hnoClause : selectActiveCardinalityClauseGrounding ontology config.state config.active
        config.active_le = none)
      (candidate : WitnessCandidate (Fin nodeCount) Concept Role)
      (hselect : selectEqUnblockedUnwitnessed config.state.base parent ancestors =
        some candidate)
      (hfull : ¬config.active < nodeCount)
  | minimumFrontier
      (hnoApart : selectEqualityApartClash config.state = none)
      (hnoClash : selectCardinalityConceptClash config.state = none)
      (hnoClause : selectActiveCardinalityClauseGrounding ontology config.state config.active
        config.active_le = none)
      (hnoWitness : selectEqUnblockedUnwitnessed config.state.base parent ancestors = none)
      (site : IndexedCardinalitySite definitions nodeCount)
      (hselect : selectIndexedExpandableMinimum definitions config.state parent ancestors
        config.expanded = some site)
      (hoverflow : ¬config.active + (definitions.get site.1).bound ≤ nodeCount)
  | terminal
      (hnoApart : selectEqualityApartClash config.state = none)
      (hnoClash : selectCardinalityConceptClash config.state = none)
      (hnoClause : selectActiveCardinalityClauseGrounding ontology config.state config.active
        config.active_le = none)
      (hnoWitness : selectEqUnblockedUnwitnessed config.state.base parent ancestors = none)
      (hnoMinimum : selectIndexedExpandableMinimum definitions config.state parent ancestors
        config.expanded = none)
      (hnoMaximum : selectIndexedViolatingMaximum definitions config.state = none)

/-- The total finite first-obstruction control in production priority order. -/
noncomputable def cardinalityControl
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount)) :
    CardinalityControlOutcome ontology definitions config parent ancestors := by
  classical
  generalize hapart : selectEqualityApartClash config.state = apart
  cases apart with
  | some candidate =>
      exact .step (.equalityApart candidate hapart)
  | none =>
      generalize hclash : selectCardinalityConceptClash config.state = clash
      cases clash with
      | some candidate =>
          exact .step (.conceptClash hapart candidate hclash)
      | none =>
          generalize hclause : selectActiveCardinalityClauseGrounding ontology config.state
            config.active config.active_le = clause
          cases clause with
          | some grounding =>
              exact .step (.branch hapart hclash grounding hclause)
          | none =>
              generalize hwitness : selectEqUnblockedUnwitnessed config.state.base parent
                ancestors = witness
              cases witness with
              | some candidate =>
                  by_cases hfit : config.active < nodeCount
                  · exact .step (.witness hapart hclash hclause candidate hwitness hfit
                      config.inactive_fresh)
                  · exact .witnessFrontier hapart hclash hclause candidate hwitness hfit
              | none =>
                  generalize hminimum : selectIndexedExpandableMinimum definitions config.state
                    parent ancestors config.expanded = minimum
                  cases minimum with
                  | some site =>
                      by_cases hfit : config.active + (definitions.get site.1).bound ≤ nodeCount
                      · exact .step (.minimum hapart hclash hclause hwitness site hminimum hfit
                          config.inactive_fresh)
                      · exact .minimumFrontier hapart hclash hclause hwitness site hminimum hfit
                  | none =>
                      generalize hmaximum : selectIndexedViolatingMaximum definitions config.state =
                        maximum
                      cases maximum with
                      | some site =>
                          have hfound := firstMatch_eq_some_mem
                            (by simpa [selectIndexedViolatingMaximum] using hmaximum)
                          have hwidth :=
                            (indexedMaximumSiteBool_eq_true_iff definitions config.state site).mp
                              hfound.2 |>.2.2
                          exact .step (.maximum hapart hclash hclause hwitness hminimum site
                            hmaximum hwidth config.inactive_fresh)
                      | none =>
                          exact .terminal hapart hclash hclause hwitness hminimum hmaximum

theorem cardinalityControl_total
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (config : CardinalityRuntimeConfig Concept Role definitions nodeCount)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount)) :
    ∃ outcome : CardinalityControlOutcome ontology definitions config parent ancestors,
      outcome = cardinalityControl ontology definitions config parent ancestors :=
  ⟨_, rfl⟩

def CardinalityControlOutcome.IsStop
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {config : CardinalityRuntimeConfig Concept Role definitions nodeCount}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)} :
    CardinalityControlOutcome ontology definitions config parent ancestors → Prop
  | .step _ => False
  | .witnessFrontier .. => True
  | .minimumFrontier .. => True
  | .terminal .. => True

/-- Reflexive-transitive descent through exact production children. -/
inductive CardinalityProductionDescends
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount)) :
    CardinalityRuntimeConfig Concept Role definitions nodeCount →
      CardinalityRuntimeConfig Concept Role definitions nodeCount → Prop where
  | refl (config) : CardinalityProductionDescends ontology definitions parent ancestors
      config config
  | tail (config child leaf)
      (step : CardinalityProductionStep ontology definitions config.state parent ancestors
        config.expanded config.active config.active_le)
      (hchild : step.ChildConfig config parent ancestors child)
      (rest : CardinalityProductionDescends ontology definitions parent ancestors child leaf) :
      CardinalityProductionDescends ontology definitions parent ancestors config leaf

/-- Finite-budget production search either constructs a sound closed
refutation or reaches an explicit frontier/terminal control state. -/
theorem cardinalityControl_search_total
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role))
    (nodeCount : Nat)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount)) :
    ∀ root : CardinalityRuntimeConfig Concept Role definitions nodeCount,
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions root.state ∨
        ∃ leaf, CardinalityProductionDescends ontology definitions parent ancestors root leaf ∧
          (cardinalityControl ontology definitions leaf parent ancestors).IsStop := by
  apply cardinalityProduction_induction ontology definitions nodeCount parent ancestors
  intro config ih
  generalize hcontrol : cardinalityControl ontology definitions config parent ancestors = outcome
  cases outcome with
  | step selected =>
      by_cases hall : ∀ child, selected.ChildConfig config parent ancestors child →
          ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions child.state
      · exact Or.inl (selected.closedRefutes_of_childConfigs config parent ancestors hall)
      · push_neg at hall
        rcases hall with ⟨child, hchild, hnotClosed⟩
        rcases ih selected child hchild with hclosed | ⟨leaf, hdescends, hstop⟩
        · exact (hnotClosed hclosed).elim
        · exact Or.inr ⟨leaf,
            .tail config child leaf selected hchild hdescends, hstop⟩
  | witnessFrontier hnoApart hnoClash hnoClause candidate hselect hfull =>
      exact Or.inr ⟨config, .refl config, by
        rw [hcontrol]
        trivial⟩
  | minimumFrontier hnoApart hnoClash hnoClause hnoWitness site hselect hoverflow =>
      exact Or.inr ⟨config, .refl config, by
        rw [hcontrol]
        trivial⟩
  | terminal hnoApart hnoClash hnoClause hnoWitness hnoMinimum hnoMaximum =>
      exact Or.inr ⟨config, .refl config, by
        rw [hcontrol]
        trivial⟩

/-- A stopped control remains inconclusive unless it is a terminal accompanied
by an independently accepted global model certificate. -/
def CardinalityControlOutcome.IsCheckedFrontier
    [Fintype Variable] [DecidableEq Variable]
    [Fintype Concept] [DecidableEq Concept]
    [Fintype Role] [DecidableEq Role]
    {ontology : List (Clause Variable Concept Role)}
    {definitions : List (CardinalityDef Concept Role)}
    {config : CardinalityRuntimeConfig Concept Role definitions nodeCount}
    {parent : Fin nodeCount → Option (Fin nodeCount)}
    {ancestors : Fin nodeCount → List (Fin nodeCount)}
    (hasCheckedModel : Prop) :
    CardinalityControlOutcome ontology definitions config parent ancestors → Prop
  | .step _ => False
  | .witnessFrontier .. => True
  | .minimumFrontier .. => True
  | .terminal .. => ¬hasCheckedModel

/-- Finite production search with the independent model checker composed at
terminal states. The SAT disjunct requires accepted model evidence; rejected
terminal evidence and node frontiers remain explicit. -/
theorem cardinalityControl_checked_semantic_or_frontier
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (nodeCount : Nat)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount)) :
    ∀ root : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount)
        definitions nodeCount,
      ClosedDistinctCardinalityRefutes (Fin nodeCount) ontology definitions root.state ∨
        CardinalityHasNonemptyModel ontology definitions ∨
          ∃ leaf,
            CardinalityProductionDescends ontology definitions parent ancestors root leaf ∧
            (cardinalityControl ontology definitions leaf parent ancestors).IsCheckedFrontier
              (HasCheckedCardinalityModel (nodeCount := nodeCount) ontology definitions) := by
  intro root
  rcases cardinalityControl_search_total ontology definitions nodeCount parent ancestors root with
    hclosed | ⟨leaf, hdescends, hstop⟩
  · exact Or.inl hclosed
  · generalize hcontrol : cardinalityControl ontology definitions leaf parent ancestors = outcome
    cases outcome with
    | step selected =>
        rw [hcontrol] at hstop
        exact hstop.elim
    | witnessFrontier hnoApart hnoClash hnoClause candidate hselect hfull =>
        exact Or.inr (Or.inr ⟨leaf, hdescends, by rw [hcontrol]; trivial⟩)
    | minimumFrontier hnoApart hnoClash hnoClause hnoWitness site hselect hoverflow =>
        exact Or.inr (Or.inr ⟨leaf, hdescends, by rw [hcontrol]; trivial⟩)
    | terminal hnoApart hnoClash hnoClause hnoWitness hnoMinimum hnoMaximum =>
        by_cases hmodel : HasCheckedCardinalityModel (nodeCount := nodeCount)
            ontology definitions
        · exact Or.inr (Or.inl (hasCardinalityModel_of_checked hmodel))
        · exact Or.inr (Or.inr ⟨leaf, hdescends, by
            rw [hcontrol]
            exact hmodel⟩)

#print axioms CardinalityProductionStep.closedRefutes_of_children
#print axioms selectIndexedExpandableMinimum_eq_none_iff
#print axioms selectIndexedExpandableMinimum_closedRefutes
#print axioms selectIndexedExpandableMinimum_source_lt_active
#print axioms selectIndexedViolatingMaximum_eq_none_iff
#print axioms selectIndexedViolatingMaximum_closedRefutes
#print axioms selectIndexedViolatingMaximum_source_lt_active
#print axioms CardinalityRuntimeConfig.mem_progressFacts
#print axioms EqState.eqGuardedFacts_materializeMinimum_subset
#print axioms CardinalityRuntimeConfig.minimumChild_progress
#print axioms cardinalityStrictGrowth_wellFounded
#print axioms mem_allActiveGroundings_properties
#print axioms selectActiveCardinalityClauseGrounding_properties
#print axioms selectActiveCardinalityClauseGrounding_closedRefutes
#print axioms CardinalityRuntimeConfig.clauseChild_progress
#print axioms DistinctEqState.lt_active_of_obligation
#print axioms selectCardinalityWitness_source_lt_active
#print axioms CardinalityRuntimeConfig.witnessChild_progress
#print axioms rustMaximumPrefixVector_lt_active
#print axioms EqState.eqGuardedFacts_merge_ssubset
#print axioms CardinalityRuntimeConfig.maximumChild_progress
#print axioms CardinalityProductionStep.child_strictGrowth
#print axioms CardinalityProductionStep.closedRefutes_of_childConfigs
#print axioms cardinalityProduction_induction
#print axioms cardinalityControl_total
#print axioms cardinalityControl_search_total
#print axioms cardinalityControl_checked_semantic_or_frontier

end ContextCalculus.Hypertableau
