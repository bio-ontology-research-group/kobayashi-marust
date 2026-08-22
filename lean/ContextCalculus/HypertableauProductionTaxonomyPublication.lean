import ContextCalculus.HypertableauProductionTaxonomyTotal

/-!
# Exact publication from total production HT search

The total-search theorems construct proof-carrying decisions for every named
taxonomy cell.  This module closes the semantic publication endpoint: those
decisions determine a Boolean for every concept and ordered subsumption pair,
and each Boolean is true exactly when its indexed source-level proposition
holds.  Negative answers therefore remain checked countermodels rather than
omitted positive results.
-/

namespace ContextCalculus.Hypertableau

/-- A complete Boolean taxonomy indexed by its exact semantic propositions. -/
structure ExactBooleanTaxonomyPublication
    (named : List Concept)
    (conceptSemantics : Concept → Prop)
    (subsumptionSemantics : Concept → Concept → Prop) where
  conceptAnswer : ∀ concept, concept ∈ named → Bool
  conceptExact : ∀ concept hnamed,
    conceptAnswer concept hnamed = true ↔ conceptSemantics concept
  subsumptionAnswer : ∀ sub, sub ∈ named → ∀ sup, sup ∈ named → Bool
  subsumptionExact : ∀ sub hsub sup hsup,
    subsumptionAnswer sub hsub sup hsup = true ↔
      subsumptionSemantics sub sup

/-- A total ordinary production route publishes every taxonomy cell exactly. -/
theorem CertifiedHTProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTProductionTaxonomyRoute conceptCount roleCount
      variableCount ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConcept ontology) (EntailsSub ontology)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

/-- A total cardinality production route publishes every taxonomy cell
exactly, retaining the complete number-restriction semantics in each index. -/
theorem CertifiedHTCardinalityProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTCardinalityProductionTaxonomyRoute conceptCount roleCount
      variableCount ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConceptWithCardinality ontology definitions)
      (EntailsSubWithCardinality ontology definitions)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

/-- A total native-ABox production route publishes every taxonomy cell against
the same complete named-individual interpretation. -/
theorem CertifiedHTNativeABoxProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTNativeABoxProductionTaxonomyRoute conceptCount roleCount
      variableCount abox ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWith ontology)
      (abox.EntailsSubWith ontology)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

/-- A total native-ABox/cardinality production route publishes every taxonomy
cell against both the complete ABox and all projected number restrictions. -/
theorem CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWithCardinality ontology definitions)
      (abox.EntailsSubWithCardinality ontology definitions)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

/-- Equality-free learned-fold production publishes every taxonomy cell
exactly after its proved inner retry loop and outer node-budget doubling. -/
theorem CertifiedHTFreshFoldProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFreshFoldProductionTaxonomyRoute conceptCount roleCount
      variableCount ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConcept ontology) (EntailsSub ontology)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

theorem CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConceptWithCardinality ontology definitions)
      (EntailsSubWithCardinality ontology definitions)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

theorem CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWith ontology)
      (abox.EntailsSubWith ontology)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

theorem CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWithCardinality ontology definitions)
      (abox.EntailsSubWithCardinality ontology definitions)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

/-! ## Current two-level assignment and expansion routes -/

theorem CertifiedHTFoldAssignmentProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFoldAssignmentProductionTaxonomyRoute conceptCount
      roleCount variableCount ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConcept ontology) (EntailsSub ontology)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

theorem CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConceptWithCardinality ontology definitions)
      (EntailsSubWithCardinality ontology definitions)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

theorem CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWith ontology)
      (abox.EntailsSubWith ontology)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

theorem CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute.publishesExactly
    (route : CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWithCardinality ontology definitions)
      (abox.EntailsSubWithCardinality ontology definitions)) := by
  rcases route.decides with ⟨certificate⟩
  exact ⟨{
    conceptAnswer := fun concept hnamed =>
      (certificate.concept concept hnamed).answer
    conceptExact := fun concept hnamed =>
      (certificate.concept concept hnamed).answer_eq_true_iff
    subsumptionAnswer := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer
    subsumptionExact := fun sub hsub sup hsup =>
      (certificate.subsumption sub hsub sup hsup).answer_eq_true_iff
  }⟩

#print axioms CertifiedHTProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTCardinalityProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTNativeABoxProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTNativeABoxCardinalityProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFreshFoldProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFreshFoldCardinalityProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFreshFoldNativeABoxProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFreshFoldNativeABoxCardinalityProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFoldAssignmentProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute.publishesExactly
#print axioms CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute.publishesExactly

end ContextCalculus.Hypertableau
