import ContextCalculus.HypertableauCardinalityRuntimeSearch
import ContextCalculus.HypertableauCardinalityCertificate
import ContextCalculus.HypertableauCardinalityFrontierWire
import ContextCalculus.HypertableauEqualityNormalization

/-!
# Checked bounded cardinality-aware HT outcomes

The concrete distinct-cardinality decision search reports a checked quotient
model, checked closure, or exhaustion of its node budget. The first two are
semantically conclusive; frontier exhaustion is not.
-/

namespace ContextCalculus.Hypertableau

abbrev CardinalityHasNonemptyModel
    (ontology : List (Clause Variable Concept Role))
    (definitions : List (CardinalityDef Concept Role)) : Prop :=
  ∃ (Domain : Type) (I : Interp Domain Concept Role),
    Nonempty Domain ∧ I.models ontology ∧ I.modelsCardinalityDefs definitions

inductive CheckedCardinalityDecisionOutcome
    (conceptCount roleCount variableCount : Nat)
    (ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) : Type where
  | sat
      {nodeCount : Nat}
      (certificate : FiniteEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (hontology : certificate.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hcheck : certificate.checkEqSatWithCardinality definitions = true)
  | closed
      {nodeCount depth : Nat}
      (certificate : FiniteDistinctEqCertificate
        nodeCount conceptCount roleCount variableCount)
      (tree : FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
      (hontology : certificate.base.base.ontology = ontology)
      (hnonempty : 0 < nodeCount)
      (hempty : certificate.base.EmptyRoot)
      (hapart : certificate.apart = [])
      (hcheck : tree.checkClosed definitions certificate = true)
  | frontier
      (document : WireCardinalityAddressFrontier)
      (hconcepts : document.concept_count = conceptCount)
      (hroles : document.role_count = roleCount)
      (hdefinitions : document.definition_count = definitions.length)
      (hcheck : document.check = true)

def CheckedCardinalityDecisionOutcome.Semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount ontology definitions) : Prop :=
  match outcome with
  | .sat .. => CardinalityHasNonemptyModel ontology definitions
  | .closed .. => ¬CardinalityHasNonemptyModel ontology definitions
  | .frontier .. => False

def CheckedCardinalityDecisionOutcome.SourceSemantics
    {target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    (source : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount target definitions) : Prop :=
  match outcome with
  | .sat .. => CardinalityHasNonemptyModel source definitions
  | .closed .. => ¬CardinalityHasNonemptyModel source definitions
  | .frontier .. => False

theorem CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount target definitions)
    (equivalent : ModelEquivalent source target)
    (hsemantics : outcome.Semantics) :
    outcome.SourceSemantics source := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      simp only [CheckedCardinalityDecisionOutcome.Semantics,
        CheckedCardinalityDecisionOutcome.SourceSemantics,
        CardinalityHasNonemptyModel] at hsemantics ⊢
      rcases hsemantics with ⟨Domain, I, hdomain, htarget, hdefinitions⟩
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr htarget, hdefinitions⟩
  | closed certificate tree hontology hnonempty hempty hapart hcheck =>
      simp only [CheckedCardinalityDecisionOutcome.Semantics,
        CheckedCardinalityDecisionOutcome.SourceSemantics,
        CardinalityHasNonemptyModel] at hsemantics ⊢
      rintro ⟨Domain, I, hdomain, hsource, hdefinitions⟩
      exact hsemantics ⟨Domain, I, hdomain,
        (equivalent Domain I).mp hsource, hdefinitions⟩
  | frontier document hconcepts hroles hdefinitions hcheck =>
      exact hsemantics

theorem CheckedCardinalityDecisionOutcome.sat_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount : Nat}
    (certificate : FiniteEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (hontology : certificate.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hcheck : certificate.checkEqSatWithCardinality definitions = true) :
    CardinalityHasNonemptyModel ontology definitions := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hmodels := certificate.checkEqSatWithCardinality_models definitions hcheck
  refine ⟨certificate.state.QuotientDomain, certificate.state.quotientCanonical, ?_, ?_, hmodels.2⟩
  · exact ⟨Quotient.mk certificate.state.nodeSetoid (Classical.choice inferInstance)⟩
  · simpa [hontology] using hmodels.1

theorem CheckedCardinalityDecisionOutcome.closed_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    {nodeCount depth : Nat}
    (certificate : FiniteDistinctEqCertificate
      nodeCount conceptCount roleCount variableCount)
    (tree : FiniteDistinctCardinalityRefutationTree
      nodeCount conceptCount roleCount variableCount depth)
    (hontology : certificate.base.base.ontology = ontology)
    (hnonempty : 0 < nodeCount)
    (hempty : certificate.base.EmptyRoot)
    (hapart : certificate.apart = [])
    (hcheck : tree.checkClosed definitions certificate = true) :
    ¬CardinalityHasNonemptyModel ontology definitions := by
  letI : Nonempty (Fin nodeCount) := ⟨⟨0, hnonempty⟩⟩
  have hnot := tree.checkClosed_ontology_unsatisfiable
    definitions certificate hempty hapart hcheck
  simpa [CardinalityHasNonemptyModel, hontology] using hnot

theorem CheckedCardinalityDecisionOutcome.conclusive_semantics
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (outcome : CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount ontology definitions) :
    (match outcome with | .frontier .. => False | _ => True) →
      outcome.Semantics := by
  cases outcome with
  | sat certificate hontology hnonempty hcheck =>
      intro _
      exact CheckedCardinalityDecisionOutcome.sat_semantics
        certificate hontology hnonempty hcheck
  | closed certificate tree hontology hnonempty hempty hapart hcheck =>
      intro _
      exact CheckedCardinalityDecisionOutcome.closed_semantics
        certificate tree hontology hnonempty hempty hapart hcheck
  | frontier document hconcepts hroles hdefinitions hcheck => simp

/-- For a fixed cardinality vocabulary and maximum minimum width, checked
tagged frontiers cannot persist through iterative doubling. Hence some round
returns a checked model or checked refutation. -/
theorem checked_cardinality_doubling_decides
    {ontology : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (maxWidth : Nat)
    (run : Nat → CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount ontology definitions)
    (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ round)
    (hwidth : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth) :
    ∃ round, (run round).Semantics := by
  classical
  by_contra hconclusive
  have hnone : ∀ round, ¬(run round).Semantics := not_exists.mp hconclusive
  have hfrontier : ∀ round, ∃ document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck := by
    intro round
    generalize houtcome : run round = outcome
    cases outcome with
    | sat certificate hontology hnonempty hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedCardinalityDecisionOutcome.sat_semantics
            certificate hontology hnonempty hcheck)
    | closed certificate tree hontology hnonempty hempty hapart hcheck =>
        exfalso
        exact hnone round (by
          rw [houtcome]
          exact CheckedCardinalityDecisionOutcome.closed_semantics
            certificate tree hontology hnonempty hempty hapart hcheck)
    | frontier document hconcepts hroles hdefinitions hcheck =>
        exact ⟨document, hconcepts, hroles, hdefinitions, hcheck, rfl⟩
  choose document hconcepts hroles hdefinitions hchecks heq using hfrontier
  obtain ⟨round, hrejected⟩ :=
    cardinality_doubling_eventually_rejects_checked_frontier
      document conceptCount roleCount definitions.length maxWidth
      (fun round => hnodes round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
      hconcepts hroles hdefinitions
      (fun round => hwidth round (document round) (hconcepts round)
        (hroles round) (hdefinitions round) (hchecks round) (heq round))
  exact hrejected (hchecks round)

theorem checked_cardinality_doubling_decides_source
    {source target : List
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))}
    {definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))}
    (equivalent : ModelEquivalent source target)
    (maxWidth : Nat)
    (run : Nat → CheckedCardinalityDecisionOutcome
      conceptCount roleCount variableCount target definitions)
    (hnodes : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.node_count = 8 * 2 ^ round)
    (hwidth : ∀ round document hconcepts hroles hdefinitions hcheck,
      run round = .frontier document hconcepts hroles hdefinitions hcheck →
        document.max_width = maxWidth) :
    ∃ round, (run round).SourceSemantics source := by
  obtain ⟨round, hsemantics⟩ :=
    checked_cardinality_doubling_decides maxWidth run hnodes hwidth
  exact ⟨round, (run round).source_semantics_of_equivalent equivalent hsemantics⟩

#print axioms CheckedCardinalityDecisionOutcome.sat_semantics
#print axioms CheckedCardinalityDecisionOutcome.closed_semantics
#print axioms CheckedCardinalityDecisionOutcome.conclusive_semantics
#print axioms checked_cardinality_doubling_decides
#print axioms CheckedCardinalityDecisionOutcome.source_semantics_of_equivalent
#print axioms checked_cardinality_doubling_decides_source

end ContextCalculus.Hypertableau
