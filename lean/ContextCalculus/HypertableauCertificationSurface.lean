import ContextCalculus.HypertableauProductionGlobalPublication
import ContextCalculus.HypertableauProductionTaxonomyPublication

/-!
# Current production hypertableau certification surface

This module names only the publication endpoints backed by KM's current
complete-assignment, forbidden-pair expansion, and frontier-doubling runtime.
Older producer interfaces remain useful as intermediate lemmas, but they are
not part of this certification surface.

Each endpoint publishes both Boolean directions for its exact semantic index.
The route arguments contain the checked source normalization, finite terminal,
frontier, and concrete computed-outcome classification evidence required by
the corresponding production family.
-/

namespace ContextCalculus.Hypertableau

theorem certifiedHTGlobalPublication
    {semantics : Prop}
    (route : CertifiedHTAssignmentProductionGlobalRoute semantics) :
    Nonempty (ExactBooleanGlobalPublication semantics) :=
  route.publishesExactly

theorem certifiedHTRegularTaxonomyPublication
    (route : CertifiedHTFoldAssignmentProductionTaxonomyRoute conceptCount
      roleCount variableCount ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConcept ontology) (EntailsSub ontology)) :=
  route.publishesExactly

theorem certifiedHTCardinalityTaxonomyPublication
    (route : CertifiedHTFoldAssignmentCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (UnsatisfiableConceptWithCardinality ontology definitions)
      (EntailsSubWithCardinality ontology definitions)) :=
  route.publishesExactly

theorem certifiedHTNativeABoxTaxonomyPublication
    (route : CertifiedHTFoldAssignmentNativeABoxProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWith ontology)
      (abox.EntailsSubWith ontology)) :=
  route.publishesExactly

theorem certifiedHTNativeABoxCardinalityTaxonomyPublication
    (route : CertifiedHTFoldAssignmentNativeABoxCardinalityProductionTaxonomyRoute
      conceptCount roleCount variableCount abox ontology definitions named) :
    Nonempty (ExactBooleanTaxonomyPublication named
      (abox.UnsatisfiableConceptWithCardinality ontology definitions)
      (abox.EntailsSubWithCardinality ontology definitions)) :=
  route.publishesExactly

#print axioms certifiedHTGlobalPublication
#print axioms certifiedHTRegularTaxonomyPublication
#print axioms certifiedHTCardinalityTaxonomyPublication
#print axioms certifiedHTNativeABoxTaxonomyPublication
#print axioms certifiedHTNativeABoxCardinalityTaxonomyPublication

end ContextCalculus.Hypertableau
