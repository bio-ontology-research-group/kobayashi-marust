import ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication
import ContextCalculus.HTMixedCardinalityCommonSourceWire

/-!
# Mixed-cardinality taxonomy publications over the common source

This executable boundary binds every exact-cardinality matrix cell to the
checked mixed Skolem projection.  It retains the normalized source, finite
dimensions, directional definitions, and complementary-pair provenance.
-/

namespace ContextCalculus.HTMixedCardinalityTaxonomyCommonPublication

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire
open ContextCalculus.HTMixedCardinalityCommonSourceWire
open ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication

structure WireMixedCardinalityTaxonomyPublication where
  version : Nat
  common : WireMixedCardinalityCommonSource
  document : WireSourceBoundCardinalityTaxonomy
deriving Lean.FromJson, Lean.ToJson, Repr

def WireMixedCardinalityTaxonomyPublication.sourceBoundB
    (wire : WireMixedCardinalityTaxonomyPublication) : Bool :=
  decide (
    wire.common.projection.mixed.variable_count =
      wire.document.source.certificate.variable_count ∧
    wire.common.projection.mixed.concepts.length =
      wire.document.source.certificate.concept_count ∧
    wire.common.projection.mixed.roles.length =
      wire.document.source.certificate.role_count ∧
    wire.common.projection.mixed.target =
      normalizedSourceClauses wire.document.source ∧
    wire.document.source.certificate.definitions.map cardinalityDefinitionKey =
      wire.common.projection.definitions.map
        (cardinalityDefinitionKey ∘ projectionDefinitionWire) ∧
    wire.document.source.certificate.exact_maximums =
      projectionExactMaximumIndices wire.common.projection.definitions ∧
    wire.document.source.certificate.exact_definitions =
      projectionExactMinimumIndices wire.common.projection.definitions)

def mixedConceptEntryBoundTo
    (entry : ExactCardinalityConceptEntry)
    (target : DecodedNormalizedCardinalityTaxonomyCertificate)
    (exact : DecodedExactCardinalityTaxonomyCertificate) : Prop :=
  entry.cell.natOntology = mapOntology target.target.ontology ∧
    entry.cell.natDefinitions = target.target.definitions.map mapCardinalityDef ∧
    entry.cell.natExactDefinitions.toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset

def mixedSubsumptionEntryBoundTo
    (entry : ExactCardinalitySubsumptionEntry)
    (target : DecodedNormalizedCardinalityTaxonomyCertificate)
    (exact : DecodedExactCardinalityTaxonomyCertificate) : Prop :=
  entry.cell.natOntology = mapOntology target.target.ontology ∧
    entry.cell.natDefinitions = target.target.definitions.map mapCardinalityDef ∧
    entry.cell.natExactDefinitions.toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset

instance {entry : ExactCardinalityConceptEntry}
    {target : DecodedNormalizedCardinalityTaxonomyCertificate}
    {exact : DecodedExactCardinalityTaxonomyCertificate} :
    Decidable (mixedConceptEntryBoundTo entry target exact) := by
  unfold mixedConceptEntryBoundTo
  infer_instance

instance {entry : ExactCardinalitySubsumptionEntry}
    {target : DecodedNormalizedCardinalityTaxonomyCertificate}
    {exact : DecodedExactCardinalityTaxonomyCertificate} :
    Decidable (mixedSubsumptionEntryBoundTo entry target exact) := by
  unfold mixedSubsumptionEntryBoundTo
  infer_instance

structure DecodedMixedCardinalityTaxonomyPublication where
  common : DecodedMixedCardinalityCommonSource
  taxonomy : DecodedNormalizedCardinalityTaxonomyCertificate
  exact : DecodedExactCardinalityTaxonomyCertificate
  variableCount : common.projection.mixed.variableCount = taxonomy.target.variableCount
  conceptCount : common.projection.mixed.concepts.length = taxonomy.target.conceptCount
  roleCount : common.projection.mixed.roles.length = taxonomy.target.roleCount
  sourceExact : mapOntology common.projection.mixed.target =
    mapOntology taxonomy.normalization.source
  definitionsExact : common.natDefinitions =
    taxonomy.target.definitions.map mapCardinalityDef
  pairedExact : (pairedExactDefinitions common.projection.semanticPairs |>
    List.map mapCardinalityDef).toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset
  conceptCellsBound : exact.covered.concepts.Forall fun entry =>
    mixedConceptEntryBoundTo entry taxonomy exact
  subsumptionCellsBound : exact.covered.subsumptions.Forall fun entry =>
    mixedSubsumptionEntryBoundTo entry taxonomy exact

def WireMixedCardinalityTaxonomyPublication.decode
    (wire : WireMixedCardinalityTaxonomyPublication) :
    Except String DecodedMixedCardinalityTaxonomyPublication := do
  if _hversion : wire.version = 1 then
    if _hdocument : wire.document.check = true then
      if _hbound : wire.sourceBoundB = true then do
        let common ← wire.common.decode
        let taxonomy ← wire.document.source.decode
        let exact ← wire.document.source.certificate.decodeExact
        if hv : common.projection.mixed.variableCount = taxonomy.target.variableCount then
          if hc : common.projection.mixed.concepts.length = taxonomy.target.conceptCount then
            if hr : common.projection.mixed.roles.length = taxonomy.target.roleCount then
              if hs : mapOntology common.projection.mixed.target =
                  mapOntology taxonomy.normalization.source then
                if hd : common.natDefinitions =
                    taxonomy.target.definitions.map mapCardinalityDef then
                  if hp : (pairedExactDefinitions common.projection.semanticPairs |>
                      List.map mapCardinalityDef).toFinset =
                      (exact.exactDefinitions.map mapCardinalityDef).toFinset then
                    if hconcepts : exact.covered.concepts.Forall fun entry =>
                        mixedConceptEntryBoundTo entry taxonomy exact then
                      if hsubs : exact.covered.subsumptions.Forall fun entry =>
                          mixedSubsumptionEntryBoundTo entry taxonomy exact then
                        return {
                          common, taxonomy, exact
                          variableCount := hv
                          conceptCount := hc
                          roleCount := hr
                          sourceExact := hs
                          definitionsExact := hd
                          pairedExact := hp
                          conceptCellsBound := hconcepts
                          subsumptionCellsBound := hsubs
                        }
                      else throw "a mixed-cardinality subsumption cell has a different target"
                    else throw "a mixed-cardinality concept cell has a different target"
                  else throw "mixed-cardinality exact definitions lack pair provenance"
                else throw "mixed-cardinality directional definitions differ"
              else throw "mixed-cardinality target differs from normalized source"
            else throw "mixed-cardinality role dimension differs"
          else throw "mixed-cardinality concept dimension differs"
        else throw "mixed-cardinality variable dimension differs"
      else throw "mixed-cardinality source and publication are not bound"
    else throw "source-bound mixed-cardinality taxonomy rejected"
  else throw s!"unsupported mixed-cardinality publication version {wire.version}"

def WireMixedCardinalityTaxonomyPublication.check
    (wire : WireMixedCardinalityTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedMixedCardinalityTaxonomyPublication.subsumption_answer_iff_common
    (decoded : DecodedMixedCardinalityTaxonomyPublication)
    (entry : ExactCardinalitySubsumptionEntry)
    (hentry : entry ∈ decoded.exact.covered.subsumptions)
    (sub sup : Fin decoded.common.projection.mixed.concepts.length)
    (hsub : entry.sub = sub.val) (hsup : entry.sup = sup.val) :
    entry.natDecision.answer = true ↔ decoded.common.CommonEntails sub sup := by
  have hbound := (List.forall_iff_forall_mem.mp decoded.subsumptionCellsBound)
    entry hentry
  rcases hbound with ⟨hontology, hdefinitions, hexact⟩
  let targetSub : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount sub
  let targetSup : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount sup
  have hnormalized := (entailsWithExact_mapModelEquivalent_iff
    decoded.taxonomy.normalization.equivalent
    (decoded.taxonomy.target.definitions.map mapCardinalityDef)
    (decoded.exact.exactDefinitions.map mapCardinalityDef)
    targetSub.val targetSup.val).symm
  calc
    entry.natDecision.answer = true ↔
        EntailsSubWithExactCardinality entry.cell.natOntology
          entry.cell.natDefinitions entry.cell.natExactDefinitions
          entry.sub entry.sup := entry.natDecision.answer_eq_true_iff
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.target.ontology)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val := by
        rw [hontology, hdefinitions, hsub, hsup]
        simpa [targetSub, targetSup] using
          (entailsWithExact_congr_toFinset
            (ontology := mapOntology decoded.taxonomy.target.ontology)
            (definitions := decoded.taxonomy.target.definitions.map mapCardinalityDef)
            (sub := sub.val) (sup := sup.val) hexact)
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val := hnormalized
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.common.projection.mixed.target)
          decoded.common.natDefinitions
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          sub.val sup.val := by
        rw [decoded.sourceExact, decoded.definitionsExact]
        simp [targetSub, targetSup]
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.common.projection.mixed.target)
          decoded.common.natDefinitions
          ((pairedExactDefinitions decoded.common.projection.semanticPairs).map
            mapCardinalityDef) sub.val sup.val :=
      entailsWithExact_congr_toFinset decoded.pairedExact.symm
    _ ↔ EntailsSubWithExactCardinality decoded.common.projection.mixed.target
          decoded.common.projection.definitions
          (pairedExactDefinitions decoded.common.projection.semanticPairs) sub sup :=
      (entailsWithExact_mapOntology_iff decoded.common.projection.mixed.target
        decoded.common.projection.definitions
        (pairedExactDefinitions decoded.common.projection.semanticPairs) sub sup).symm
    _ ↔ decoded.common.TargetEntails sub sup :=
      decoded.common.exact_entails_iff_target sub sup
    _ ↔ decoded.common.CommonEntails sub sup :=
      (decoded.common.entails_target_iff sub sup).symm

theorem DecodedMixedCardinalityTaxonomyPublication.concept_answer_iff_target
    (decoded : DecodedMixedCardinalityTaxonomyPublication)
    (entry : ExactCardinalityConceptEntry)
    (hentry : entry ∈ decoded.exact.covered.concepts)
    (concept : Fin decoded.common.projection.mixed.concepts.length)
    (hconcept : entry.coordinate = concept.val) :
    entry.natDecision.answer = true ↔
      decoded.common.TargetUnsatisfiable concept := by
  have hbound := (List.forall_iff_forall_mem.mp decoded.conceptCellsBound)
    entry hentry
  rcases hbound with ⟨hontology, hdefinitions, hexact⟩
  let targetConcept : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount concept
  have hnormalized := (unsatisfiableWithExact_mapModelEquivalent_iff
    decoded.taxonomy.normalization.equivalent
    (decoded.taxonomy.target.definitions.map mapCardinalityDef)
    (decoded.exact.exactDefinitions.map mapCardinalityDef)
    targetConcept.val).symm
  calc
    entry.natDecision.answer = true ↔
        UnsatisfiableConceptWithExactCardinality entry.cell.natOntology
          entry.cell.natDefinitions entry.cell.natExactDefinitions
          entry.coordinate := entry.natDecision.answer_eq_true_iff
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.target.ontology)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val := by
        rw [hontology, hdefinitions, hconcept]
        simpa [targetConcept] using
          (unsatisfiableWithExact_congr_toFinset
            (ontology := mapOntology decoded.taxonomy.target.ontology)
            (definitions := decoded.taxonomy.target.definitions.map mapCardinalityDef)
            (concept := concept.val) hexact)
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val := hnormalized
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.common.projection.mixed.target)
          decoded.common.natDefinitions
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          concept.val := by
        rw [decoded.sourceExact, decoded.definitionsExact]
        simp [targetConcept]
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.common.projection.mixed.target)
          decoded.common.natDefinitions
          ((pairedExactDefinitions decoded.common.projection.semanticPairs).map
            mapCardinalityDef) concept.val :=
      unsatisfiableWithExact_congr_toFinset decoded.pairedExact.symm
    _ ↔ UnsatisfiableConceptWithExactCardinality
          decoded.common.projection.mixed.target decoded.common.projection.definitions
          (pairedExactDefinitions decoded.common.projection.semanticPairs) concept :=
      (unsatisfiableWithExact_mapOntology_iff decoded.common.projection.mixed.target
        decoded.common.projection.definitions
        (pairedExactDefinitions decoded.common.projection.semanticPairs) concept).symm
    _ ↔ decoded.common.TargetUnsatisfiable concept :=
      decoded.common.exact_unsatisfiable_iff_target concept

theorem DecodedMixedCardinalityTaxonomyPublication.concept_answer_iff_common
    (decoded : DecodedMixedCardinalityTaxonomyPublication)
    (entry : ExactCardinalityConceptEntry)
    (hentry : entry ∈ decoded.exact.covered.concepts)
    (concept : Fin decoded.common.projection.mixed.concepts.length)
    (hconcept : entry.coordinate = concept.val) :
    entry.natDecision.answer = true ↔
      decoded.common.CommonUnsatisfiable concept :=
  (decoded.concept_answer_iff_target entry hentry concept hconcept).trans
    (decoded.common.unsatisfiable_target_iff concept).symm

def DecodedMixedCardinalityTaxonomyPublication.CommonSubsumptionSemantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) : Prop :=
  ∀ sub sup : Fin decoded.common.projection.mixed.concepts.length,
    sub.val ∈ decoded.exact.namedNats → sup.val ∈ decoded.exact.namedNats →
    ∃ entry : ExactCardinalitySubsumptionEntry,
      entry ∈ decoded.exact.covered.subsumptions ∧
      entry.sub = sub.val ∧ entry.sup = sup.val ∧
      (entry.natDecision.answer = true ↔ decoded.common.CommonEntails sub sup)

def DecodedMixedCardinalityTaxonomyPublication.TargetConceptSemantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) : Prop :=
  ∀ concept : Fin decoded.common.projection.mixed.concepts.length,
    concept.val ∈ decoded.exact.namedNats →
    ∃ entry : ExactCardinalityConceptEntry,
      entry ∈ decoded.exact.covered.concepts ∧
      entry.coordinate = concept.val ∧
      (entry.natDecision.answer = true ↔
        decoded.common.TargetUnsatisfiable concept)

def DecodedMixedCardinalityTaxonomyPublication.CommonConceptSemantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) : Prop :=
  ∀ concept : Fin decoded.common.projection.mixed.concepts.length,
    concept.val ∈ decoded.exact.namedNats →
    ∃ entry : ExactCardinalityConceptEntry,
      entry ∈ decoded.exact.covered.concepts ∧
      entry.coordinate = concept.val ∧
      (entry.natDecision.answer = true ↔
        decoded.common.CommonUnsatisfiable concept)

def DecodedMixedCardinalityTaxonomyPublication.CommonSemantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) : Prop :=
  decoded.CommonConceptSemantics ∧ decoded.CommonSubsumptionSemantics

theorem DecodedMixedCardinalityTaxonomyPublication.common_subsumption_semantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) :
    decoded.CommonSubsumptionSemantics := by
  intro sub sup hsub hsup
  rcases decoded.exact.covered.subsumptionCovered sub.val hsub sup.val hsup with
    ⟨entry, hentry, hsubCoordinate, hsupCoordinate⟩
  exact ⟨entry, hentry, hsubCoordinate, hsupCoordinate,
    decoded.subsumption_answer_iff_common entry hentry sub sup
      hsubCoordinate hsupCoordinate⟩

theorem DecodedMixedCardinalityTaxonomyPublication.target_concept_semantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) :
    decoded.TargetConceptSemantics := by
  intro concept hnamed
  rcases decoded.exact.covered.conceptCovered concept.val hnamed with
    ⟨entry, hentry, hcoordinate⟩
  exact ⟨entry, hentry, hcoordinate,
    decoded.concept_answer_iff_target entry hentry concept hcoordinate⟩

theorem DecodedMixedCardinalityTaxonomyPublication.common_concept_semantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) :
    decoded.CommonConceptSemantics := by
  intro concept hnamed
  rcases decoded.exact.covered.conceptCovered concept.val hnamed with
    ⟨entry, hentry, hcoordinate⟩
  exact ⟨entry, hentry, hcoordinate,
    decoded.concept_answer_iff_common entry hentry concept hcoordinate⟩

theorem DecodedMixedCardinalityTaxonomyPublication.common_semantics
    (decoded : DecodedMixedCardinalityTaxonomyPublication) :
    decoded.CommonSemantics :=
  ⟨decoded.common_concept_semantics, decoded.common_subsumption_semantics⟩

theorem WireMixedCardinalityTaxonomyPublication.check_subsumption_sound
    (wire : WireMixedCardinalityTaxonomyPublication)
    (decoded : DecodedMixedCardinalityTaxonomyPublication)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true) :
    decoded.CommonSubsumptionSemantics := decoded.common_subsumption_semantics

theorem WireMixedCardinalityTaxonomyPublication.check_target_concept_sound
    (wire : WireMixedCardinalityTaxonomyPublication)
    (decoded : DecodedMixedCardinalityTaxonomyPublication)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true) :
    decoded.TargetConceptSemantics := decoded.target_concept_semantics

def WireMixedCardinalityTaxonomyPublication.SemanticallyValid
    (wire : WireMixedCardinalityTaxonomyPublication) : Prop :=
  ∃ decoded : DecodedMixedCardinalityTaxonomyPublication,
    wire.decode = .ok decoded ∧ decoded.CommonSemantics

theorem WireMixedCardinalityTaxonomyPublication.check_sound
    (wire : WireMixedCardinalityTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireMixedCardinalityTaxonomyPublication.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, hdecode, decoded.common_semantics⟩

#print axioms WireMixedCardinalityTaxonomyPublication.check_subsumption_sound
#print axioms WireMixedCardinalityTaxonomyPublication.check_target_concept_sound
#print axioms WireMixedCardinalityTaxonomyPublication.check_sound

end ContextCalculus.HTMixedCardinalityTaxonomyCommonPublication
