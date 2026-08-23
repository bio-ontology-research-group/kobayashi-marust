import ContextCalculus.HTMixedTaxonomyCommonPublication
import ContextCalculus.HTBundleCommonSourceWire

/-!
# Bundle HT taxonomy publications over the common routing source

Bundle projection introduces target-only definer concepts.  This boundary
checks the complete projected ontology against the normalized publication and
uses the projection's injective source-concept embedding when interpreting
every published taxonomy coordinate.
-/

namespace ContextCalculus.HTBundleTaxonomyCommonPublication

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTDirectCommonSourceWire
open ContextCalculus.HTBundleCommonSourceWire
open ContextCalculus.HTMixedTaxonomyCommonPublication

structure WireBundleTaxonomyPublication where
  version : Nat
  common : WireBundleCommonSource
  document : WireSourceBoundOrdinaryTaxonomy
deriving Lean.FromJson, Lean.ToJson, Repr

def WireBundleTaxonomyPublication.sourceBoundB
    (wire : WireBundleTaxonomyPublication) : Bool :=
  decide (
    wire.common.projection.variable_count = taxonomyVariableCount wire.document.source ∧
    wire.common.projection.concepts.length = taxonomyConceptCount wire.document.source ∧
    wire.common.projection.roles.length = taxonomyRoleCount wire.document.source ∧
    wire.common.projection.target = taxonomySourceClauses wire.document.source)

inductive DecodedBundleTaxonomyPublication where
  | plain (common : DecodedBundleCommonSource)
      (taxonomy : DecodedNormalizedPlainTaxonomy)
      (variableCount : common.projection.variableCount = taxonomy.target.variableCount)
      (conceptCount : common.projection.concepts.length = taxonomy.target.conceptCount)
      (roleCount : common.projection.roles.length = taxonomy.target.roleCount)
      (sourceExact : mapOntology common.projection.target =
        mapOntology taxonomy.normalization.source)
  | mixed (common : DecodedBundleCommonSource)
      (taxonomy : DecodedNormalizedMixedTaxonomy)
      (variableCount : common.projection.variableCount = taxonomy.target.variableCount)
      (conceptCount : common.projection.concepts.length = taxonomy.target.conceptCount)
      (roleCount : common.projection.roles.length = taxonomy.target.roleCount)
      (sourceExact : mapOntology common.projection.target =
        mapOntology taxonomy.normalization.source)

def WireBundleTaxonomyPublication.decode
    (wire : WireBundleTaxonomyPublication) :
    Except String DecodedBundleTaxonomyPublication :=
  if _hversion : wire.version = 1 then
    if _hdocument : wire.document.check = true then
      if _hbound : wire.sourceBoundB = true then do
        let common ← wire.common.decode
        let taxonomy ← wire.document.source.decode
        match taxonomy with
        | .plain decoded =>
            if hv : common.projection.variableCount = decoded.target.variableCount then
              if hc : common.projection.concepts.length = decoded.target.conceptCount then
                if hr : common.projection.roles.length = decoded.target.roleCount then
                  if hs : mapOntology common.projection.target =
                      mapOntology decoded.normalization.source then
                    return .plain common decoded hv hc hr hs
                  else throw "decoded bundle target differs from publication source"
                else throw "decoded bundle role dimension differs from publication"
              else throw "decoded bundle concept dimension differs from publication"
            else throw "decoded bundle variable dimension differs from publication"
        | .mixed decoded =>
            if hv : common.projection.variableCount = decoded.target.variableCount then
              if hc : common.projection.concepts.length = decoded.target.conceptCount then
                if hr : common.projection.roles.length = decoded.target.roleCount then
                  if hs : mapOntology common.projection.target =
                      mapOntology decoded.normalization.source then
                    return .mixed common decoded hv hc hr hs
                  else throw "decoded bundle target differs from publication source"
                else throw "decoded bundle role dimension differs from publication"
              else throw "decoded bundle concept dimension differs from publication"
            else throw "decoded bundle variable dimension differs from publication"
      else .error "bundle source and HT publication describe different ontologies"
    else .error "source-bound HT taxonomy publication rejected"
  else .error s!"unsupported bundle HT common-publication version {wire.version}"

def WireBundleTaxonomyPublication.check
    (wire : WireBundleTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedBundleTaxonomyPublication.CommonSemantics :
    DecodedBundleTaxonomyPublication → Prop
  | .plain common taxonomy _ conceptCount _ _ =>
      ∀ sub sup : Fin common.projection.sourceConcepts.length,
        Fin.cast conceptCount (common.projection.sourceTargets sub) ∈ taxonomy.target.named →
        Fin.cast conceptCount (common.projection.sourceTargets sup) ∈ taxonomy.target.named →
        ((Fin.cast conceptCount (common.projection.sourceTargets sub),
            Fin.cast conceptCount (common.projection.sourceTargets sup)) ∈
            taxonomy.semantic.subsumptions ↔ common.CommonEntails sub sup)
  | .mixed common taxonomy _ conceptCount _ _ =>
      ∀ sub sup : Fin common.projection.sourceConcepts.length,
        Fin.cast conceptCount (common.projection.sourceTargets sub) ∈ taxonomy.target.named →
        Fin.cast conceptCount (common.projection.sourceTargets sup) ∈ taxonomy.target.named →
        ((Fin.cast conceptCount (common.projection.sourceTargets sub),
            Fin.cast conceptCount (common.projection.sourceTargets sup)) ∈
            taxonomy.semantic.subsumptions ↔ common.CommonEntails sub sup)

theorem DecodedBundleTaxonomyPublication.common_semantics
    (decoded : DecodedBundleTaxonomyPublication) : decoded.CommonSemantics := by
  cases decoded with
  | plain common taxonomy hv hc hr hexact =>
      intro sub sup hsub hsup
      rw [taxonomy.subsumptions_exact _ _ hsub hsup]
      rw [← target_entails_source_iff common.projection.target
        taxonomy.normalization.source hc hexact
        (common.projection.sourceTargets sub) (common.projection.sourceTargets sup)]
      exact (common.entails_target_iff sub sup).symm
  | mixed common taxonomy hv hc hr hexact =>
      intro sub sup hsub hsup
      rw [taxonomy.subsumptions_exact _ _ hsub hsup]
      rw [← target_entails_source_iff common.projection.target
        taxonomy.normalization.source hc hexact
        (common.projection.sourceTargets sub) (common.projection.sourceTargets sup)]
      exact (common.entails_target_iff sub sup).symm

def WireBundleTaxonomyPublication.SemanticallyValid
    (wire : WireBundleTaxonomyPublication) : Prop :=
  wire.document.runs.check = true ∧
    wire.document.payloadBoundB = true ∧
    ∃ decoded : DecodedBundleTaxonomyPublication,
      wire.decode = .ok decoded ∧ decoded.CommonSemantics

theorem WireBundleTaxonomyPublication.check_sound
    (wire : WireBundleTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  have hdecodeOk : ∃ decoded, wire.decode = .ok decoded := by
    cases hdecode : wire.decode with
    | error message => simp [WireBundleTaxonomyPublication.check, hdecode] at hcheck
    | ok decoded => exact ⟨decoded, rfl⟩
  rcases hdecodeOk with ⟨decoded, hdecode⟩
  have hdocument : wire.document.check = true := by
    by_contra hfalse
    by_cases hversion : wire.version = 1 <;>
      simp [WireBundleTaxonomyPublication.decode, hversion, hfalse] at hdecode
  have hsourceBound := wire.document.check_sound hdocument
  exact ⟨hsourceBound.2.1, hsourceBound.2.2.1, decoded,
    hdecode, decoded.common_semantics⟩

#print axioms DecodedBundleTaxonomyPublication.common_semantics
#print axioms WireBundleTaxonomyPublication.check_sound

end ContextCalculus.HTBundleTaxonomyCommonPublication
