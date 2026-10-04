import ContextCalculus.DatatypeClassTransport
import ContextCalculus.FunctionalDatatypeQuotient
import ContextCalculus.IntegerProfileCover
import ContextCalculus.SelectedSubjectTaxonomyPublication
import ContextCalculus.DLSafeRulePath
import ContextCalculus.DLSafeRuleForest
import ContextCalculus.SourceSubsumerClosure
import ContextCalculus.DataABoxProjection
import ContextCalculus.DataDomainCardinality
import ContextCalculus.DataAssertionNormalization
import ContextCalculus.FiniteDatatypeCover
import ContextCalculus.SingletonMergeClash
import ContextCalculus.DLSafeAtomicTaxonomyExtension
import ContextCalculus.DatatypeValueEmbedding
import ContextCalculus.ReflexiveRoleNormalization
import ContextCalculus.NativeCardinalityNormalization
import ContextCalculus.HypertableauProductionGlobalPublication
import ContextCalculus.HypertableauProductionTaxonomyPublication
import ContextCalculus.HypertableauCardinalityTaxonomyRunMatrixWire
import ContextCalculus.HypertableauOrdinaryTaxonomyRunMatrixWire
import ContextCalculus.HypertableauSourceBoundNativeABoxWire
import ContextCalculus.HypertableauExecutablePublicationWire
import ContextCalculus.HTDirectTaxonomyCommonPublication
import ContextCalculus.HTMixedTaxonomyCommonPublication
import ContextCalculus.HTBundleTaxonomyCommonPublication
import ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication
import ContextCalculus.HTMixedCardinalityTaxonomyCommonPublication
import ContextCalculus.HTBundleCardinalityTaxonomyCommonPublication

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

/-- The source-bound ordinary taxonomy publication derives its common routing
source from the decoded publication source itself. The direct checker rejects
existential sources rather than accepting an independently supplied adapter. -/
theorem certifiedHTDirectCommonTaxonomyPublication
    (wire : HTDirectTaxonomyCommonPublication.WireDirectTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid :=
  wire.check_sound hcheck

/-- A checked mixed publication reports the complete named taxonomy of the
exact common unary-Skolem source retained by its projection. -/
theorem certifiedHTMixedCommonTaxonomyPublication
    (wire : HTMixedTaxonomyCommonPublication.WireMixedTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid :=
  wire.check_sound hcheck

/-- A checked bundle publication reports the complete named taxonomy of its
exact common shared-function source at the checked source-concept embedding. -/
theorem certifiedHTBundleCommonTaxonomyPublication
    (wire : HTBundleTaxonomyCommonPublication.WireBundleTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid :=
  wire.check_sound hcheck

/-- The direct cardinality route publishes every named concept status and
subsumption against the exact common source, including complementary-pair
recognition obligations. -/
theorem certifiedHTDirectCardinalityCommonTaxonomyPublication
    (wire : HTDirectCardinalityTaxonomyCommonPublication.WireDirectCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid :=
  wire.check_sound hcheck

/-- The mixed cardinality route composes the retained unary-Skolem functions
with disjoint cardinality witness functions and publishes the exact taxonomy
of that common source. -/
theorem certifiedHTMixedCardinalityCommonTaxonomyPublication
    (wire : HTMixedCardinalityTaxonomyCommonPublication.WireMixedCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid :=
  wire.check_sound hcheck

/-- The bundle cardinality route publishes source-concept answers through its
checked injective embedding into the expanded target vocabulary. -/
theorem certifiedHTBundleCardinalityCommonTaxonomyPublication
    (wire : HTBundleCardinalityTaxonomyCommonPublication.WireBundleCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid :=
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
#print axioms certifiedHTDirectCommonTaxonomyPublication
#print axioms certifiedHTMixedCommonTaxonomyPublication
#print axioms certifiedHTBundleCommonTaxonomyPublication
#print axioms certifiedHTDirectCardinalityCommonTaxonomyPublication
#print axioms certifiedHTMixedCardinalityCommonTaxonomyPublication
#print axioms certifiedHTBundleCardinalityCommonTaxonomyPublication

#print axioms ContextCalculus.NativeCardinalityNormalization.maximum_complement_recognition
#print axioms ContextCalculus.NativeCardinalityNormalization.minimum_definition_extension_iff
#print axioms ContextCalculus.NativeCardinalityNormalization.maximum_definition_extension_iff

end ContextCalculus.Hypertableau

#print axioms ContextCalculus.DatatypeValueEmbedding.singleton_equality
#print axioms ContextCalculus.ReflexiveRoleNormalization.reflexive_iff_global_self
#print axioms ContextCalculus.ReflexiveRoleNormalization.universal_at_subject
#print axioms ContextCalculus.ReflexiveRoleNormalization.no_successor_of_self_contradictory_class
#print axioms ContextCalculus.DatatypeValueEmbedding.distinct_values_clash
#print axioms ContextCalculus.DatatypeValueEmbedding.value_concept_equality
#print axioms ContextCalculus.DatatypeValueEmbedding.functional_role_iff

-- Named graph extension obligations for SWRL class queries.
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.range_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.inverse_functionality_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.symmetry_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.asymmetry_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.irreflexivity_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.disjoint_roles_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.data_domain_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.boolean_old_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.boolean_fresh_valuation
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.role_path_old_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.role_path_cannot_end_fresh
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.role_chain_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.boolean_domain_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.boolean_range_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.boolean_data_domain_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.pointwise_extension
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.named_edges_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.named_classes_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.taxonomy_countermodel
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.boolean_query_projection_exact
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.domain_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.transitivity_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.functionality_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.inclusion_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.inverse_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.named_atoms_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.named_rule_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.data_range_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.data_functionality_preserved
#print axioms ContextCalculus.DLSafeAtomicTaxonomyExtension.guarded_named_rules_preserved

#print axioms ContextCalculus.SingletonMergeClash.distinct_conflict
#print axioms ContextCalculus.SingletonMergeClash.opposite_label_conflict

#print axioms ContextCalculus.FiniteDatatypeCover.cover_iff

#print axioms ContextCalculus.FiniteDatatypeCover.alias_cover

#print axioms ContextCalculus.FiniteDatatypeCover.singleton_cover_excludes_distinct_successors

#print axioms ContextCalculus.DataAssertionNormalization.has_value_iff

#print axioms ContextCalculus.DataAssertionNormalization.alias_assertion_iff

#print axioms ContextCalculus.DataAssertionNormalization.negative_alias_assertion_iff

#print axioms ContextCalculus.DataAssertionNormalization.fresh_definition_extension

#print axioms ContextCalculus.DataDomainCardinality.zero_domain_iff_empty

#print axioms ContextCalculus.DataDomainCardinality.existential_class_empty

#print axioms ContextCalculus.SingletonMergeClash.same_iff_nominal

#print axioms ContextCalculus.DataABoxProjection.functionality_iff

#print axioms ContextCalculus.DataABoxProjection.domain_iff

#print axioms ContextCalculus.DataABoxProjection.range_iff

#print axioms ContextCalculus.DataABoxProjection.inclusion_preserved

#print axioms ContextCalculus.SourceSubsumerClosure.sound
#print axioms ContextCalculus.SourceSubsumerClosure.model_preserved

#print axioms ContextCalculus.DLSafeRulePath.rolling_iff
#print axioms ContextCalculus.DLSafeRulePath.endpoint_compilation_iff
#print axioms ContextCalculus.DLSafeRuleForest.body_only_elimination
#print axioms ContextCalculus.DLSafeRuleForest.named_cover_exists
#print axioms ContextCalculus.DLSafeRuleForest.independent_branches

#print axioms ContextCalculus.Hypertableau.selectedSubjectPublicPublication

-- Supporting numeric lemmas: parser refinement and whole-source coverage
-- require their own evidence; these reports alone do not certify the rewrite.
#print axioms ContextCalculus.DatatypeValueEmbedding.has_value_iff
#print axioms ContextCalculus.DatatypeValueEmbedding.disjunctive_has_value_iff
#print axioms ContextCalculus.DatatypeValueEmbedding.subproperty_iff
#print axioms ContextCalculus.FunctionalDatatypeQuotient.functional_preserved
#print axioms ContextCalculus.FunctionalDatatypeQuotient.exists_preserved
#print axioms ContextCalculus.FunctionalDatatypeQuotient.forall_preserved
#print axioms ContextCalculus.FunctionalDatatypeQuotient.literal_assertion_preserved
#print axioms ContextCalculus.FunctionalDatatypeQuotient.cardinality_preserved
#print axioms ContextCalculus.FunctionalDatatypeQuotient.maximum_cardinality_preserved
#print axioms ContextCalculus.FunctionalDatatypeQuotient.exact_cardinality_preserved
#print axioms ContextCalculus.IntegerProfileCover.cut_cover
#print axioms ContextCalculus.IntegerProfileCover.same_profile
#print axioms ContextCalculus.IntegerProfileCover.predicate_family_cover
#print axioms ContextCalculus.IntegerProfileCover.deduplicated_family_cover

#print axioms ContextCalculus.IntegerProfileCover.bounded_cut_cover

#print axioms ContextCalculus.DatatypeClassTransport.atLeast_congr
#print axioms ContextCalculus.DatatypeClassTransport.class_preserved
#print axioms ContextCalculus.DatatypeClassTransport.tbox_preserved

#print axioms ContextCalculus.DatatypeClassTransport.abox_preserved
