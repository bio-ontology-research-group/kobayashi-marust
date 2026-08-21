import ContextCalculus.HypertableauCardinalityProductionSearch
import ContextCalculus.HypertableauCardinalityDistinctWire

/-!
# Concrete cardinality production runtime fields

This module checks and decodes the Rust fields that determine logical
cardinality recursion: the distinct equality state, `active_nodes`, and the
branch-local set of expanded `(definition_id, source)` minimum sites.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure FiniteCardinalityRuntimeFields
    (nodeCount conceptCount roleCount variableCount : Nat)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) where
  certificate : FiniteDistinctEqCertificate
    nodeCount conceptCount roleCount variableCount
  activeNodes : Nat
  expandedMinimums : List (IndexedCardinalitySite definitions nodeCount)

def FiniteCardinalityRuntimeFields.check
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions) : Bool :=
  fields.certificate.inactivePrefixFreshB fields.activeNodes &&
    decide fields.expandedMinimums.Nodup &&
    fields.expandedMinimums.all fun site =>
      decide ((definitions.get site.1).kind = .minimum) &&
        decide (site.2.1 < fields.activeNodes)

def FiniteCardinalityRuntimeFields.toConfig
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) :
    CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount) definitions nodeCount where
  state := fields.certificate.state
  active := fields.activeNodes
  expanded := fields.expandedMinimums.toFinset
  active_le := by
    simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true] at hcheck
    exact fields.certificate.inactivePrefixFreshB_fit fields.activeNodes hcheck.1.1
  inactive_fresh := by
    simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true] at hcheck
    exact fields.certificate.inactivePrefixFreshB_sound fields.activeNodes hcheck.1.1

@[simp] theorem FiniteCardinalityRuntimeFields.toConfig_state
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) :
    (fields.toConfig hcheck).state = fields.certificate.state := rfl

@[simp] theorem FiniteCardinalityRuntimeFields.toConfig_active
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) :
    (fields.toConfig hcheck).active = fields.activeNodes := rfl

@[simp] theorem FiniteCardinalityRuntimeFields.mem_toConfig_expanded
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true)
    (site : IndexedCardinalitySite definitions nodeCount) :
    site ∈ (fields.toConfig hcheck).expanded ↔ site ∈ fields.expandedMinimums := by
  classical
  simp [FiniteCardinalityRuntimeFields.toConfig]

theorem FiniteCardinalityRuntimeFields.expandedMinimums_nodup
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true) : fields.expandedMinimums.Nodup := by
  simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  exact hcheck.1.2

theorem FiniteCardinalityRuntimeFields.expanded_kind
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true)
    (site : IndexedCardinalitySite definitions nodeCount)
    (hsite : site ∈ fields.expandedMinimums) :
    (definitions.get site.1).kind = .minimum := by
  simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hcheck
  exact (hcheck.2 site hsite).1

theorem FiniteCardinalityRuntimeFields.expanded_source_lt_active
    (fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions)
    (hcheck : fields.check = true)
    (site : IndexedCardinalitySite definitions nodeCount)
    (hsite : site ∈ fields.expandedMinimums) : site.2.1 < fields.activeNodes := by
  simp only [FiniteCardinalityRuntimeFields.check, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at hcheck
  exact (hcheck.2 site hsite).2

structure WireExpandedMinimum where
  definition : Nat
  source : Nat
deriving FromJson, ToJson, Repr

structure WireCardinalityRuntimeFields where
  state : WireDistinctEqState
  active_nodes : Nat
  expanded_minimums : List WireExpandedMinimum
deriving FromJson, ToJson, Repr

def WireCardinalityRuntimeFields.decode
    (wire : WireCardinalityRuntimeFields)
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Except String
      (FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
        definitions) := do
  let certificate ← wire.state.decode nodeCount conceptCount roleCount variableCount ontology
  let expandedMinimums ← wire.expanded_minimums.mapM fun site => do
    return (← checkedFin "expanded minimum definition" definitions.length site.definition,
      ← checkedFin "expanded minimum source" nodeCount site.source)
  return ⟨certificate, wire.active_nodes, expandedMinimums⟩

structure CheckedCardinalityRuntimeFields
    (nodeCount conceptCount roleCount variableCount : Nat)
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) where
  fields : FiniteCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
    definitions
  valid : fields.check = true

def WireCardinalityRuntimeFields.decodeChecked
    (wire : WireCardinalityRuntimeFields)
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List
      (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Except String
      (CheckedCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
        definitions) := do
  let fields ← wire.decode nodeCount conceptCount roleCount variableCount ontology definitions
  if hvalid : fields.check = true then
    return ⟨fields, hvalid⟩
  else
    throw "invalid cardinality runtime fields"

theorem CheckedCardinalityRuntimeFields.has_config
    (checked : CheckedCardinalityRuntimeFields nodeCount conceptCount roleCount variableCount
      definitions) :
    ∃ config : CardinalityRuntimeConfig (Fin conceptCount) (Fin roleCount) definitions nodeCount,
      config = checked.fields.toConfig checked.valid :=
  ⟨_, rfl⟩

/-! ## Checked logical transitions

Rust stores expanded minimum sites in a `HashSet`, so wire-list order is not
logical state. Clause, witness, and maximum recursion preserve that set;
minimum recursion inserts exactly its selected site. -/

def FiniteDistinctEqCertificate.matchesLogicalStateB
    (actual expected : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount) : Bool :=
  decide (actual.base.base.ontology = expected.base.base.ontology) &&
    decide (actual.base.base.labels = expected.base.base.labels) &&
    decide (actual.base.base.edges = expected.base.base.edges) &&
    decide (actual.base.base.obligations = expected.base.base.obligations) &&
    decide (actual.base.equalities = expected.base.equalities) &&
    decide (actual.apart = expected.apart)

theorem FiniteDistinctEqCertificate.matchesLogicalStateB_state
    (actual expected : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hcheck : actual.matchesLogicalStateB expected = true) :
    actual.state = expected.state := by
  simp only [FiniteDistinctEqCertificate.matchesLogicalStateB, Bool.and_eq_true,
    decide_eq_true_eq] at hcheck
  rcases hcheck with
    ⟨⟨⟨⟨⟨hontology, hlabels⟩, hedges⟩, hobligations⟩, hequalities⟩, hapart⟩
  apply DistinctEqState.ext
  · apply EqState.ext
    · apply State.ext
      · funext node lit
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state]
        rw [hlabels]
      · funext role source target
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state]
        rw [hedges]
      · funext role filler node
        simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state,
          FiniteSatCertificate.state]
        rw [hobligations]
    · simp only [FiniteDistinctEqCertificate.state, FiniteEqCertificate.state]
      rw [hequalities]
  · funext left right
    simp only [FiniteDistinctEqCertificate.state]
    rw [hapart]

theorem CardinalityRuntimeConfig.extensional
    {left right : CardinalityRuntimeConfig Concept Role definitions nodeCount}
    (hstate : left.state = right.state) (hactive : left.active = right.active)
    (hexpanded : left.expanded = right.expanded) : left = right := by
  cases left
  cases right
  simp_all

def FiniteCardinalityRuntimeFields.sameExpandedB
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions) : Bool :=
  decide (∀ site : IndexedCardinalitySite definitions nodeCount,
    site ∈ next.expandedMinimums ↔ site ∈ current.expandedMinimums)

def FiniteCardinalityRuntimeFields.insertedExpandedB
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (inserted : IndexedCardinalitySite definitions nodeCount) : Bool :=
  decide (∀ site : IndexedCardinalitySite definitions nodeCount,
    site ∈ next.expandedMinimums ↔ site = inserted ∨ site ∈ current.expandedMinimums)

def FiniteCardinalityRuntimeFields.clauseTransitionB
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (assignment : Fin variableCount → Fin nodeCount)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) : Bool :=
  current.certificate.transitionB next.certificate assignment atom &&
    decide (next.activeNodes = current.activeNodes) && current.sameExpandedB next

def FiniteCardinalityRuntimeFields.witnessTransitionB
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (source target : Fin nodeCount) (role : Fin roleCount)
    (filler : Lit (Fin conceptCount)) : Bool :=
  next.certificate.matchesLogicalStateB
      (current.certificate.materializeWitness source target role filler) &&
    decide (next.activeNodes = current.activeNodes + 1) && current.sameExpandedB next

def FiniteCardinalityRuntimeFields.minimumTransitionB
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (site : IndexedCardinalitySite definitions nodeCount)
    (targets : Fin (definitions.get site.1).bound → Fin nodeCount) : Bool :=
  current.certificate.minimumTransitionB next.certificate site.2 targets
      (definitions.get site.1).role (definitions.get site.1).filler &&
    decide (next.activeNodes = current.activeNodes + (definitions.get site.1).bound) &&
    current.insertedExpandedB next site

def FiniteCardinalityRuntimeFields.maximumTransitionB
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (left right : Fin nodeCount) : Bool :=
  current.certificate.mergeTransitionB next.certificate left right &&
    decide (next.activeNodes = current.activeNodes) && current.sameExpandedB next

theorem FiniteCardinalityRuntimeFields.clauseTransitionB_config
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (hcurrent : current.check = true) (hnext : next.check = true)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    {grounding : Grounding (Fin variableCount) (Fin nodeCount)
      (Fin conceptCount) (Fin roleCount)}
    (hselect : selectActiveCardinalityClauseGrounding ontology
      (current.toConfig hcurrent).state (current.toConfig hcurrent).active
      (current.toConfig hcurrent).active_le = some grounding)
    (atom : Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
    (htransition : current.clauseTransitionB next grounding.2 atom = true) :
    next.toConfig hnext = (current.toConfig hcurrent).clauseChild ontology hselect atom := by
  simp only [FiniteCardinalityRuntimeFields.clauseTransitionB, Bool.and_eq_true,
    decide_eq_true_eq, FiniteCardinalityRuntimeFields.sameExpandedB] at htransition
  rcases htransition with ⟨⟨hstate, hactive⟩, hexpanded⟩
  apply CardinalityRuntimeConfig.extensional
  · simpa [FiniteCardinalityRuntimeFields.toConfig] using
      current.certificate.transitionB_state next.certificate grounding.2 atom hstate
  · exact hactive
  · ext site
    simp only [CardinalityRuntimeConfig.clauseChild,
      FiniteCardinalityRuntimeFields.mem_toConfig_expanded]
    exact hexpanded site

theorem FiniteCardinalityRuntimeFields.witnessTransitionB_config
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (hcurrent : current.check = true) (hnext : next.check = true)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    {candidate : WitnessCandidate (Fin nodeCount) (Fin conceptCount) (Fin roleCount)}
    (hselect : selectEqUnblockedUnwitnessed (current.toConfig hcurrent).state.base
      parent ancestors = some candidate)
    (hfit : (current.toConfig hcurrent).active < nodeCount)
    (htransition : current.witnessTransitionB next candidate.2.2
      (rustNextTarget (current.toConfig hcurrent).active nodeCount hfit)
      candidate.1 candidate.2.1 = true) :
    next.toConfig hnext = (current.toConfig hcurrent).witnessChild
      parent ancestors hselect hfit := by
  simp only [FiniteCardinalityRuntimeFields.witnessTransitionB, Bool.and_eq_true,
    decide_eq_true_eq, FiniteCardinalityRuntimeFields.sameExpandedB] at htransition
  rcases htransition with ⟨⟨hstate, hactive⟩, hexpanded⟩
  apply CardinalityRuntimeConfig.extensional
  · rw [FiniteCardinalityRuntimeFields.toConfig_state,
      FiniteDistinctEqCertificate.matchesLogicalStateB_state _ _ hstate,
      FiniteDistinctEqCertificate.state_materializeWitness]
    rfl
  · exact hactive
  · ext site
    simp only [CardinalityRuntimeConfig.witnessChild,
      FiniteCardinalityRuntimeFields.mem_toConfig_expanded]
    exact hexpanded site

theorem FiniteCardinalityRuntimeFields.minimumTransitionB_config
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (hcurrent : current.check = true) (hnext : next.check = true)
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedExpandableMinimum definitions
      (current.toConfig hcurrent).state parent ancestors
      (current.toConfig hcurrent).expanded = some site)
    (hfit : (current.toConfig hcurrent).active + (definitions.get site.1).bound ≤ nodeCount)
    (htransition : current.minimumTransitionB next site
      (rustConsecutiveTargets (current.toConfig hcurrent).active
        (definitions.get site.1).bound nodeCount hfit) = true) :
    next.toConfig hnext = (current.toConfig hcurrent).minimumChild
      parent ancestors hselect hfit := by
  simp only [FiniteCardinalityRuntimeFields.minimumTransitionB, Bool.and_eq_true,
    decide_eq_true_eq, FiniteCardinalityRuntimeFields.insertedExpandedB] at htransition
  rcases htransition with ⟨⟨hstate, hactive⟩, hexpanded⟩
  apply CardinalityRuntimeConfig.extensional
  · simpa [FiniteCardinalityRuntimeFields.toConfig] using
      current.certificate.minimumTransitionB_state next.certificate site.2
        (rustConsecutiveTargets (current.toConfig hcurrent).active
          (definitions.get site.1).bound nodeCount hfit)
        (definitions.get site.1).role (definitions.get site.1).filler hstate
  · exact hactive
  · ext candidate
    simp only [CardinalityRuntimeConfig.minimumChild,
      FiniteCardinalityRuntimeFields.mem_toConfig_expanded, Finset.mem_insert]
    exact hexpanded candidate

theorem FiniteCardinalityRuntimeFields.maximumTransitionB_config
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (hcurrent : current.check = true) (hnext : next.check = true)
    {site : IndexedCardinalitySite definitions nodeCount}
    (hselect : selectIndexedViolatingMaximum definitions
      (current.toConfig hcurrent).state = some site)
    (hwidth : (definitions.get site.1).bound + 1 ≤
      (rustMaximumRepresentatives (current.toConfig hcurrent).state
        (definitions.get site.1) site.2).length)
    (left right : Fin ((definitions.get site.1).bound + 1)) (hne : left ≠ right)
    (htransition : current.maximumTransitionB next
      (rustPrefixVector
        (rustMaximumRepresentatives (current.toConfig hcurrent).state
          (definitions.get site.1) site.2)
        ((definitions.get site.1).bound + 1) hwidth left)
      (rustPrefixVector
        (rustMaximumRepresentatives (current.toConfig hcurrent).state
          (definitions.get site.1) site.2)
        ((definitions.get site.1).bound + 1) hwidth right) = true) :
    next.toConfig hnext = (current.toConfig hcurrent).maximumChild
      hselect hwidth left right hne := by
  simp only [FiniteCardinalityRuntimeFields.maximumTransitionB, Bool.and_eq_true,
    decide_eq_true_eq, FiniteCardinalityRuntimeFields.sameExpandedB] at htransition
  rcases htransition with ⟨⟨hstate, hactive⟩, hexpanded⟩
  apply CardinalityRuntimeConfig.extensional
  · simpa [FiniteCardinalityRuntimeFields.toConfig] using
      current.certificate.mergeTransitionB_state next.certificate _ _ hstate
  · exact hactive
  · ext candidate
    simp only [CardinalityRuntimeConfig.maximumChild,
      FiniteCardinalityRuntimeFields.mem_toConfig_expanded]
    exact hexpanded candidate

/-- A concrete checked successor emitted for one selected production step.
Immediate clashes have no successors. Each recursive case uses the exact Rust
field mutation checked above. -/
def FiniteCardinalityRuntimeFields.CheckedChildTransition
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (hcurrent : current.check = true)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (step : CardinalityProductionStep ontology definitions
      (current.toConfig hcurrent).state parent ancestors
      (current.toConfig hcurrent).expanded (current.toConfig hcurrent).active
      (current.toConfig hcurrent).active_le) : Prop :=
  match step with
  | .equalityApart _ _ => False
  | .conceptClash _ _ _ => False
  | .branch _ _ grounding _ =>
      ∃ atom, atom ∈ grounding.1.head ∧
        current.clauseTransitionB next grounding.2 atom = true
  | .witness _ _ _ candidate _ hfit _ =>
      current.witnessTransitionB next candidate.2.2
        (rustNextTarget (current.toConfig hcurrent).active nodeCount hfit)
        candidate.1 candidate.2.1 = true
  | .minimum _ _ _ _ site _ hfit _ =>
      current.minimumTransitionB next site
        (rustConsecutiveTargets (current.toConfig hcurrent).active
          (definitions.get site.1).bound nodeCount hfit) = true
  | .maximum _ _ _ _ _ site _ hwidth _ =>
      ∃ left right, ∃ hne : left ≠ right,
        current.maximumTransitionB next
          (rustPrefixVector
            (rustMaximumRepresentatives (current.toConfig hcurrent).state
              (definitions.get site.1) site.2)
            ((definitions.get site.1).bound + 1) hwidth left)
          (rustPrefixVector
            (rustMaximumRepresentatives (current.toConfig hcurrent).state
              (definitions.get site.1) site.2)
            ((definitions.get site.1).bound + 1) hwidth right) = true

theorem FiniteCardinalityRuntimeFields.checkedChildTransition_childConfig
    (current next : FiniteCardinalityRuntimeFields
      nodeCount conceptCount roleCount variableCount definitions)
    (hcurrent : current.check = true) (hnext : next.check = true)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (parent : Fin nodeCount → Option (Fin nodeCount))
    (ancestors : Fin nodeCount → List (Fin nodeCount))
    (step : CardinalityProductionStep ontology definitions
      (current.toConfig hcurrent).state parent ancestors
      (current.toConfig hcurrent).expanded (current.toConfig hcurrent).active
      (current.toConfig hcurrent).active_le)
    (htransition : current.CheckedChildTransition next hcurrent ontology parent ancestors step) :
    step.ChildConfig (current.toConfig hcurrent) parent ancestors (next.toConfig hnext) := by
  cases step with
  | equalityApart candidate hselect => exact htransition.elim
  | conceptClash hnoApart candidate hselect => exact htransition.elim
  | branch hnoApart hnoClash grounding hselect =>
      rcases htransition with ⟨atom, hatom, hchecked⟩
      exact ⟨atom, hatom,
        current.clauseTransitionB_config next hcurrent hnext ontology hselect atom hchecked⟩
  | witness hnoApart hnoClash hnoClause candidate hselect hfit hprefix =>
      exact current.witnessTransitionB_config next hcurrent hnext parent ancestors
        hselect hfit htransition
  | minimum hnoApart hnoClash hnoClause hnoWitness site hselect hfit hprefix =>
      exact current.minimumTransitionB_config next hcurrent hnext parent ancestors
        hselect hfit htransition
  | maximum hnoApart hnoClash hnoClause hnoWitness hnoMinimum site hselect hwidth hprefix =>
      rcases htransition with ⟨left, right, hne, hchecked⟩
      exact ⟨left, right, hne,
        current.maximumTransitionB_config next hcurrent hnext hselect hwidth
          left right hne hchecked⟩

#print axioms FiniteCardinalityRuntimeFields.mem_toConfig_expanded
#print axioms FiniteCardinalityRuntimeFields.expandedMinimums_nodup
#print axioms FiniteCardinalityRuntimeFields.expanded_kind
#print axioms FiniteCardinalityRuntimeFields.expanded_source_lt_active
#print axioms CheckedCardinalityRuntimeFields.has_config
#print axioms FiniteCardinalityRuntimeFields.clauseTransitionB_config
#print axioms FiniteCardinalityRuntimeFields.witnessTransitionB_config
#print axioms FiniteCardinalityRuntimeFields.minimumTransitionB_config
#print axioms FiniteCardinalityRuntimeFields.maximumTransitionB_config
#print axioms FiniteCardinalityRuntimeFields.checkedChildTransition_childConfig

end ContextCalculus.Hypertableau
