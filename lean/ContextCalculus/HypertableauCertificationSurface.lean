import ContextCalculus.HypertableauProductionGlobalPublication
import ContextCalculus.HypertableauProductionTaxonomyPublication
import ContextCalculus.HypertableauCardinalityTaxonomyRunMatrixWire
import ContextCalculus.HypertableauOrdinaryTaxonomyRunMatrixWire
import ContextCalculus.HypertableauSourceBoundNativeABoxWire
import ContextCalculus.HypertableauExecutablePublicationWire

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

theorem certifiedHTCardinalityTaxonomyRunMatrixPublication
    (wire : WireCardinalityTaxonomyRunMatrix) (hcheck : wire.check = true) :
    ∃ decoded : DecodedCardinalityTaxonomyRunMatrix,
      wire.decode = .ok decoded ∧
        ∃ certificate : CompleteCardinalityTaxonomyCertificate
          decoded.terminal.ontology decoded.terminal.definitions
          decoded.terminal.named,
          certificate = decoded.terminal.semantic :=
  wire.check_sound hcheck

theorem certifiedHTOrdinaryTaxonomyRunMatrixPublication
    (wire : WireOrdinaryTaxonomyRunMatrix) (hcheck : wire.check = true) :
    ∃ decoded : DecodedOrdinaryTaxonomyRunMatrix,
      wire.decode = .ok decoded ∧
        Nonempty (CompleteTaxonomyCertificate decoded.terminal.ontology
          decoded.terminal.named) :=
  wire.check_sound hcheck

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

theorem certifiedHTSourceBoundNativeABoxGlobalPublication
    (wire : WireSourceBoundNativeABoxGlobal) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.run.check = true ∧
      wire.payloadBoundB = true :=
  wire.check_sound hcheck

theorem certifiedHTSourceBoundNativeABoxCardinalityGlobalPublication
    (wire : WireSourceBoundNativeABoxCardinalityGlobal) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.run.check = true ∧
      wire.payloadBoundB = true :=
  wire.check_sound hcheck

theorem certifiedHTSourceBoundNativeABoxTaxonomyPublication
    (wire : WireSourceBoundNativeABoxTaxonomy) (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.runs.check = true ∧
      wire.payloadBoundB = true :=
  wire.check_sound hcheck

theorem certifiedHTSourceBoundNativeABoxCardinalityTaxonomyPublication
    (wire : WireSourceBoundNativeABoxCardinalityTaxonomy)
    (hcheck : wire.check = true) :
    wire.source.SemanticallyValid ∧ wire.runs.check = true ∧
      wire.payloadBoundB = true :=
  wire.check_sound hcheck

/-- Executable global HT route selection.  The route tag is decoded from the
publication document, and every branch is source-bound to its retained run. -/
theorem certifiedHTExecutableGlobalPublication
    (wire : WireExecutableHTGlobalPublication) (hcheck : wire.check = true) :
    wire.SemanticallyValid :=
  wire.check_sound hcheck

/-- Executable complete-taxonomy HT route selection.  No abstract production
route or computed-outcome classifier is supplied as a theorem argument. -/
theorem certifiedHTExecutableTaxonomyPublication
    (wire : WireExecutableHTTaxonomyPublication) (hcheck : wire.check = true) :
    wire.SemanticallyValid :=
  wire.check_sound hcheck

#print axioms certifiedHTGlobalPublication
#print axioms certifiedHTRegularTaxonomyPublication
#print axioms certifiedHTCardinalityTaxonomyPublication
#print axioms certifiedHTCardinalityTaxonomyRunMatrixPublication
#print axioms certifiedHTOrdinaryTaxonomyRunMatrixPublication
#print axioms certifiedHTNativeABoxTaxonomyPublication
#print axioms certifiedHTNativeABoxCardinalityTaxonomyPublication
#print axioms certifiedHTSourceBoundNativeABoxGlobalPublication
#print axioms certifiedHTSourceBoundNativeABoxCardinalityGlobalPublication
#print axioms certifiedHTSourceBoundNativeABoxTaxonomyPublication
#print axioms certifiedHTSourceBoundNativeABoxCardinalityTaxonomyPublication
#print axioms certifiedHTExecutableGlobalPublication
#print axioms certifiedHTExecutableTaxonomyPublication

end ContextCalculus.Hypertableau
