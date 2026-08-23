import ContextCalculus.HTMixedCardinalityTaxonomyCommonPublication
import ContextCalculus.HTBundleCardinalityCommonSourceWire

/-!
# Bundle-cardinality taxonomy publications over the common source

Bundle projection expands the concept vocabulary.  This boundary reconstructs
the checked source-name embedding at the wire layer and binds every matrix cell
to the expanded target, while classification semantics remain stated over the
original source concepts.
-/

namespace ContextCalculus.HTBundleCardinalityTaxonomyCommonPublication

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTDirectCardinalityCommonSourceWire
open ContextCalculus.HTBundleCardinalityCommonSourceWire
open ContextCalculus.HTDirectCardinalityTaxonomyCommonPublication

def wireBundleSourceTarget (bundle : WireBundleProjection) (source : Nat) : Nat :=
  bundle.concepts.idxOf (bundle.source_concepts.getD source "")

def bundleProjectionDefinitionWire
    (bundle : WireBundleProjection)
    (definition : WireProjectionCardinalityDef) : WireCardinalityDef where
  marker := wireBundleSourceTarget bundle definition.marker
  minimum := definition.min
  bound := definition.n
  role := definition.role
  filler := wireBundleSourceTarget bundle definition.filler

structure WireBundleCardinalityTaxonomyPublication where
  version : Nat
  common : WireBundleCardinalityCommonSource
  document : WireSourceBoundCardinalityTaxonomy
deriving Lean.FromJson, Lean.ToJson, Repr

def WireBundleCardinalityTaxonomyPublication.sourceBoundB
    (wire : WireBundleCardinalityTaxonomyPublication) : Bool :=
  decide (
    wire.common.projection.bundle.variable_count =
      wire.document.source.certificate.variable_count ∧
    wire.common.projection.bundle.concepts.length =
      wire.document.source.certificate.concept_count ∧
    wire.common.projection.bundle.roles.length =
      wire.document.source.certificate.role_count ∧
    wire.common.projection.bundle.target =
      normalizedSourceClauses wire.document.source ∧
    wire.document.source.certificate.definitions.map cardinalityDefinitionKey =
      wire.common.projection.definitions.map
        (cardinalityDefinitionKey ∘
          bundleProjectionDefinitionWire wire.common.projection.bundle) ∧
    wire.document.source.certificate.exact_maximums =
      projectionExactMaximumIndices wire.common.projection.definitions ∧
    wire.document.source.certificate.exact_definitions =
      projectionExactMinimumIndices wire.common.projection.definitions)

def bundleConceptEntryBoundTo
    (entry : ExactCardinalityConceptEntry)
    (target : DecodedNormalizedCardinalityTaxonomyCertificate)
    (exact : DecodedExactCardinalityTaxonomyCertificate) : Prop :=
  entry.cell.natOntology = mapOntology target.target.ontology ∧
    entry.cell.natDefinitions = target.target.definitions.map mapCardinalityDef ∧
    entry.cell.natExactDefinitions.toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset

def bundleSubsumptionEntryBoundTo
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
    Decidable (bundleConceptEntryBoundTo entry target exact) := by
  unfold bundleConceptEntryBoundTo
  infer_instance

instance {entry : ExactCardinalitySubsumptionEntry}
    {target : DecodedNormalizedCardinalityTaxonomyCertificate}
    {exact : DecodedExactCardinalityTaxonomyCertificate} :
    Decidable (bundleSubsumptionEntryBoundTo entry target exact) := by
  unfold bundleSubsumptionEntryBoundTo
  infer_instance

structure DecodedBundleCardinalityTaxonomyPublication where
  common : DecodedBundleCardinalityCommonSource
  taxonomy : DecodedNormalizedCardinalityTaxonomyCertificate
  exact : DecodedExactCardinalityTaxonomyCertificate
  variableCount : common.projection.bundle.variableCount = taxonomy.target.variableCount
  conceptCount : common.projection.bundle.concepts.length = taxonomy.target.conceptCount
  roleCount : common.projection.bundle.roles.length = taxonomy.target.roleCount
  sourceExact : mapOntology common.projection.bundle.target =
    mapOntology taxonomy.normalization.source
  definitionsExact : common.targetDefinitions.map mapCardinalityDef =
    taxonomy.target.definitions.map mapCardinalityDef
  pairedExact : (pairedExactDefinitions common.targetPairs |>
    List.map mapCardinalityDef).toFinset =
      (exact.exactDefinitions.map mapCardinalityDef).toFinset
  conceptCellsBound : exact.covered.concepts.Forall fun entry =>
    bundleConceptEntryBoundTo entry taxonomy exact
  subsumptionCellsBound : exact.covered.subsumptions.Forall fun entry =>
    bundleSubsumptionEntryBoundTo entry taxonomy exact

def WireBundleCardinalityTaxonomyPublication.decode
    (wire : WireBundleCardinalityTaxonomyPublication) :
    Except String DecodedBundleCardinalityTaxonomyPublication := do
  if _hversion : wire.version = 1 then
    if _hdocument : wire.document.check = true then
      if _hbound : wire.sourceBoundB = true then do
        let common ← wire.common.decode
        let taxonomy ← wire.document.source.decode
        let exact ← wire.document.source.certificate.decodeExact
        if hv : common.projection.bundle.variableCount = taxonomy.target.variableCount then
          if hc : common.projection.bundle.concepts.length = taxonomy.target.conceptCount then
            if hr : common.projection.bundle.roles.length = taxonomy.target.roleCount then
              if hs : mapOntology common.projection.bundle.target =
                  mapOntology taxonomy.normalization.source then
                if hd : common.targetDefinitions.map mapCardinalityDef =
                    taxonomy.target.definitions.map mapCardinalityDef then
                  if hp : (pairedExactDefinitions common.targetPairs |>
                      List.map mapCardinalityDef).toFinset =
                      (exact.exactDefinitions.map mapCardinalityDef).toFinset then
                    if hconcepts : exact.covered.concepts.Forall fun entry =>
                        bundleConceptEntryBoundTo entry taxonomy exact then
                      if hsubs : exact.covered.subsumptions.Forall fun entry =>
                          bundleSubsumptionEntryBoundTo entry taxonomy exact then
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
                      else throw "a bundle-cardinality subsumption cell has a different target"
                    else throw "a bundle-cardinality concept cell has a different target"
                  else throw "bundle-cardinality exact definitions lack pair provenance"
                else throw "bundle-cardinality target definitions differ"
              else throw "bundle-cardinality target differs from normalized source"
            else throw "bundle-cardinality role dimension differs"
          else throw "bundle-cardinality target concept dimension differs"
        else throw "bundle-cardinality variable dimension differs"
      else throw "bundle-cardinality source and publication are not bound"
    else throw "source-bound bundle-cardinality taxonomy rejected"
  else throw s!"unsupported bundle-cardinality publication version {wire.version}"

def WireBundleCardinalityTaxonomyPublication.check
    (wire : WireBundleCardinalityTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedBundleCardinalityTaxonomyPublication.subsumption_answer_iff_common
    (decoded : DecodedBundleCardinalityTaxonomyPublication)
    (entry : ExactCardinalitySubsumptionEntry)
    (hentry : entry ∈ decoded.exact.covered.subsumptions)
    (sub sup : Fin decoded.common.projection.bundle.sourceConcepts.length)
    (hsub : entry.sub = (decoded.common.projection.bundle.sourceTargets sub).val)
    (hsup : entry.sup = (decoded.common.projection.bundle.sourceTargets sup).val) :
    entry.natDecision.answer = true ↔ decoded.common.CommonEntails sub sup := by
  have hbound := (List.forall_iff_forall_mem.mp decoded.subsumptionCellsBound)
    entry hentry
  rcases hbound with ⟨hontology, hdefinitions, hexact⟩
  let targetSub : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount (decoded.common.projection.bundle.sourceTargets sub)
  let targetSup : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount (decoded.common.projection.bundle.sourceTargets sup)
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
            (sub := (decoded.common.projection.bundle.sourceTargets sub).val)
            (sup := (decoded.common.projection.bundle.sourceTargets sup).val) hexact)
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetSub.val targetSup.val := hnormalized
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.common.projection.bundle.target)
          (decoded.common.targetDefinitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          (decoded.common.projection.bundle.sourceTargets sub).val
          (decoded.common.projection.bundle.sourceTargets sup).val := by
        rw [decoded.sourceExact, decoded.definitionsExact]
        simp [targetSub, targetSup]
    _ ↔ EntailsSubWithExactCardinality
          (mapOntology decoded.common.projection.bundle.target)
          (decoded.common.targetDefinitions.map mapCardinalityDef)
          ((pairedExactDefinitions decoded.common.targetPairs).map mapCardinalityDef)
          (decoded.common.projection.bundle.sourceTargets sub).val
          (decoded.common.projection.bundle.sourceTargets sup).val :=
      entailsWithExact_congr_toFinset decoded.pairedExact.symm
    _ ↔ EntailsSubWithExactCardinality decoded.common.projection.bundle.target
          decoded.common.targetDefinitions
          (pairedExactDefinitions decoded.common.targetPairs)
          (decoded.common.projection.bundle.sourceTargets sub)
          (decoded.common.projection.bundle.sourceTargets sup) :=
      (entailsWithExact_mapOntology_iff decoded.common.projection.bundle.target
        decoded.common.targetDefinitions
        (pairedExactDefinitions decoded.common.targetPairs)
        (decoded.common.projection.bundle.sourceTargets sub)
        (decoded.common.projection.bundle.sourceTargets sup)).symm
    _ ↔ decoded.common.TargetEntails sub sup :=
      decoded.common.exact_entails_iff_target sub sup
    _ ↔ decoded.common.CommonEntails sub sup :=
      (decoded.common.entails_target_iff sub sup).symm

theorem DecodedBundleCardinalityTaxonomyPublication.concept_answer_iff_common
    (decoded : DecodedBundleCardinalityTaxonomyPublication)
    (entry : ExactCardinalityConceptEntry)
    (hentry : entry ∈ decoded.exact.covered.concepts)
    (concept : Fin decoded.common.projection.bundle.sourceConcepts.length)
    (hconcept : entry.coordinate =
      (decoded.common.projection.bundle.sourceTargets concept).val) :
    entry.natDecision.answer = true ↔
      decoded.common.CommonUnsatisfiable concept := by
  have hbound := (List.forall_iff_forall_mem.mp decoded.conceptCellsBound)
    entry hentry
  rcases hbound with ⟨hontology, hdefinitions, hexact⟩
  let targetConcept : Fin decoded.taxonomy.target.conceptCount :=
    Fin.cast decoded.conceptCount
      (decoded.common.projection.bundle.sourceTargets concept)
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
            (concept :=
              (decoded.common.projection.bundle.sourceTargets concept).val) hexact)
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.taxonomy.normalization.source)
          (decoded.taxonomy.target.definitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          targetConcept.val := hnormalized
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.common.projection.bundle.target)
          (decoded.common.targetDefinitions.map mapCardinalityDef)
          (decoded.exact.exactDefinitions.map mapCardinalityDef)
          (decoded.common.projection.bundle.sourceTargets concept).val := by
        rw [decoded.sourceExact, decoded.definitionsExact]
        simp [targetConcept]
    _ ↔ UnsatisfiableConceptWithExactCardinality
          (mapOntology decoded.common.projection.bundle.target)
          (decoded.common.targetDefinitions.map mapCardinalityDef)
          ((pairedExactDefinitions decoded.common.targetPairs).map mapCardinalityDef)
          (decoded.common.projection.bundle.sourceTargets concept).val :=
      unsatisfiableWithExact_congr_toFinset decoded.pairedExact.symm
    _ ↔ UnsatisfiableConceptWithExactCardinality
          decoded.common.projection.bundle.target decoded.common.targetDefinitions
          (pairedExactDefinitions decoded.common.targetPairs)
          (decoded.common.projection.bundle.sourceTargets concept) :=
      (unsatisfiableWithExact_mapOntology_iff
        decoded.common.projection.bundle.target decoded.common.targetDefinitions
        (pairedExactDefinitions decoded.common.targetPairs)
        (decoded.common.projection.bundle.sourceTargets concept)).symm
    _ ↔ decoded.common.TargetUnsatisfiable concept :=
      decoded.common.exact_unsatisfiable_iff_target concept
    _ ↔ decoded.common.CommonUnsatisfiable concept :=
      (decoded.common.unsatisfiable_target_iff concept).symm

def DecodedBundleCardinalityTaxonomyPublication.CommonSubsumptionSemantics
    (decoded : DecodedBundleCardinalityTaxonomyPublication) : Prop :=
  ∀ sub sup : Fin decoded.common.projection.bundle.sourceConcepts.length,
    (decoded.common.projection.bundle.sourceTargets sub).val ∈ decoded.exact.namedNats →
    (decoded.common.projection.bundle.sourceTargets sup).val ∈ decoded.exact.namedNats →
    ∃ entry : ExactCardinalitySubsumptionEntry,
      entry ∈ decoded.exact.covered.subsumptions ∧
      entry.sub = (decoded.common.projection.bundle.sourceTargets sub).val ∧
      entry.sup = (decoded.common.projection.bundle.sourceTargets sup).val ∧
      (entry.natDecision.answer = true ↔ decoded.common.CommonEntails sub sup)

def DecodedBundleCardinalityTaxonomyPublication.CommonConceptSemantics
    (decoded : DecodedBundleCardinalityTaxonomyPublication) : Prop :=
  ∀ concept : Fin decoded.common.projection.bundle.sourceConcepts.length,
    (decoded.common.projection.bundle.sourceTargets concept).val ∈
      decoded.exact.namedNats →
    ∃ entry : ExactCardinalityConceptEntry,
      entry ∈ decoded.exact.covered.concepts ∧
      entry.coordinate =
        (decoded.common.projection.bundle.sourceTargets concept).val ∧
      (entry.natDecision.answer = true ↔
        decoded.common.CommonUnsatisfiable concept)

def DecodedBundleCardinalityTaxonomyPublication.CommonSemantics
    (decoded : DecodedBundleCardinalityTaxonomyPublication) : Prop :=
  decoded.CommonConceptSemantics ∧ decoded.CommonSubsumptionSemantics

theorem DecodedBundleCardinalityTaxonomyPublication.common_subsumption_semantics
    (decoded : DecodedBundleCardinalityTaxonomyPublication) :
    decoded.CommonSubsumptionSemantics := by
  intro sub sup hsub hsup
  rcases decoded.exact.covered.subsumptionCovered
      (decoded.common.projection.bundle.sourceTargets sub).val hsub
      (decoded.common.projection.bundle.sourceTargets sup).val hsup with
    ⟨entry, hentry, hsubCoordinate, hsupCoordinate⟩
  exact ⟨entry, hentry, hsubCoordinate, hsupCoordinate,
    decoded.subsumption_answer_iff_common entry hentry sub sup
      hsubCoordinate hsupCoordinate⟩

theorem DecodedBundleCardinalityTaxonomyPublication.common_concept_semantics
    (decoded : DecodedBundleCardinalityTaxonomyPublication) :
    decoded.CommonConceptSemantics := by
  intro concept hnamed
  rcases decoded.exact.covered.conceptCovered
      (decoded.common.projection.bundle.sourceTargets concept).val hnamed with
    ⟨entry, hentry, hcoordinate⟩
  exact ⟨entry, hentry, hcoordinate,
    decoded.concept_answer_iff_common entry hentry concept hcoordinate⟩

theorem DecodedBundleCardinalityTaxonomyPublication.common_semantics
    (decoded : DecodedBundleCardinalityTaxonomyPublication) :
    decoded.CommonSemantics :=
  ⟨decoded.common_concept_semantics, decoded.common_subsumption_semantics⟩

theorem WireBundleCardinalityTaxonomyPublication.check_sound
    (wire : WireBundleCardinalityTaxonomyPublication)
    (decoded : DecodedBundleCardinalityTaxonomyPublication)
    (_hdecode : wire.decode = .ok decoded) (_hcheck : wire.check = .ok true) :
    decoded.CommonSemantics := decoded.common_semantics

#print axioms DecodedBundleCardinalityTaxonomyPublication.common_subsumption_semantics
#print axioms WireBundleCardinalityTaxonomyPublication.check_sound

end ContextCalculus.HTBundleCardinalityTaxonomyCommonPublication
