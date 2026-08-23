import ContextCalculus.HypertableauSourceBoundOrdinaryTaxonomyWire
import ContextCalculus.HTMixedCommonSourceWire

/-!
# Mixed HT taxonomy publications over the common routing source

The mixed projection is the only component that retains the original unary
Skolem functions.  The normalized HT publication retains their complete
projected HT ontology.  This checker accepts the pair only when that ontology
is literally the normalized source carried by the publication, with identical
variable, concept, and role dimensions.  Consequently two independently valid
documents for different ontologies cannot be combined.
-/

namespace ContextCalculus.HTMixedTaxonomyCommonPublication

open ContextCalculus
open ContextCalculus.Hypertableau
open ContextCalculus.HTMixedCommonSourceWire
open ContextCalculus.HTDirectCommonSourceWire

def taxonomyVariableCount
    (wire : WireNormalizedTaxonomyCertificate) : Nat :=
  match wire.payload with
  | .plain certificate => certificate.variable_count
  | .mixed certificate => certificate.variable_count

def taxonomyConceptCount
    (wire : WireNormalizedTaxonomyCertificate) : Nat :=
  match wire.payload with
  | .plain certificate => certificate.concept_count
  | .mixed certificate => certificate.concept_count

def taxonomyRoleCount
    (wire : WireNormalizedTaxonomyCertificate) : Nat :=
  match wire.payload with
  | .plain certificate => certificate.role_count
  | .mixed certificate => certificate.role_count

def taxonomySourceClauses
    (wire : WireNormalizedTaxonomyCertificate) : List WireClause :=
  wire.normalization.map (·.source)

structure WireMixedTaxonomyPublication where
  version : Nat
  common : WireMixedCommonSource
  document : WireSourceBoundOrdinaryTaxonomy
deriving Lean.FromJson, Lean.ToJson, Repr

def WireMixedTaxonomyPublication.sourceBoundB
    (wire : WireMixedTaxonomyPublication) : Bool :=
  decide (
    wire.common.projection.variable_count = taxonomyVariableCount wire.document.source ∧
    wire.common.projection.concepts.length = taxonomyConceptCount wire.document.source ∧
    wire.common.projection.roles.length = taxonomyRoleCount wire.document.source ∧
    wire.common.projection.target = taxonomySourceClauses wire.document.source)

inductive DecodedMixedTaxonomyPublication where
  | plain (common : DecodedMixedCommonSource)
      (taxonomy : DecodedNormalizedPlainTaxonomy)
      (variableCount : common.projection.variableCount = taxonomy.target.variableCount)
      (conceptCount : common.projection.concepts.length = taxonomy.target.conceptCount)
      (roleCount : common.projection.roles.length = taxonomy.target.roleCount)
      (sourceExact : mapOntology common.projection.target =
        mapOntology taxonomy.normalization.source)
  | mixed (common : DecodedMixedCommonSource)
      (taxonomy : DecodedNormalizedMixedTaxonomy)
      (variableCount : common.projection.variableCount = taxonomy.target.variableCount)
      (conceptCount : common.projection.concepts.length = taxonomy.target.conceptCount)
      (roleCount : common.projection.roles.length = taxonomy.target.roleCount)
      (sourceExact : mapOntology common.projection.target =
        mapOntology taxonomy.normalization.source)

def WireMixedTaxonomyPublication.decode
    (wire : WireMixedTaxonomyPublication) :
    Except String DecodedMixedTaxonomyPublication :=
  if hverson : wire.version = 1 then
    if hdocument : wire.document.check = true then
      if hbound : wire.sourceBoundB = true then do
        let common ← wire.common.decode
        let taxonomy ← wire.document.source.decode
        -- The raw identity check above makes these propositions computationally
        -- decidable and ensures that the decoded finite ontologies have one source.
        match taxonomy with
        | .plain decoded =>
            if hv : common.projection.variableCount = decoded.target.variableCount then
              if hc : common.projection.concepts.length = decoded.target.conceptCount then
                if hr : common.projection.roles.length = decoded.target.roleCount then
                  if hs : mapOntology common.projection.target =
                      mapOntology decoded.normalization.source then
                    return .plain common decoded hv hc hr hs
                  else throw "decoded mixed target differs from publication source"
                else throw "decoded mixed role dimension differs from publication"
              else throw "decoded mixed concept dimension differs from publication"
            else throw "decoded mixed variable dimension differs from publication"
        | .mixed decoded =>
            if hv : common.projection.variableCount = decoded.target.variableCount then
              if hc : common.projection.concepts.length = decoded.target.conceptCount then
                if hr : common.projection.roles.length = decoded.target.roleCount then
                  if hs : mapOntology common.projection.target =
                      mapOntology decoded.normalization.source then
                    return .mixed common decoded hv hc hr hs
                  else throw "decoded mixed target differs from publication source"
                else throw "decoded mixed role dimension differs from publication"
              else throw "decoded mixed concept dimension differs from publication"
            else throw "decoded mixed variable dimension differs from publication"
      else .error "mixed source and HT publication describe different ontologies"
    else .error "source-bound HT taxonomy publication rejected"
  else .error s!"unsupported mixed HT common-publication version {wire.version}"

def WireMixedTaxonomyPublication.check
    (wire : WireMixedTaxonomyPublication) : Except String Bool := do
  let _ ← wire.decode
  return true

def DecodedMixedTaxonomyPublication.CommonSemantics :
    DecodedMixedTaxonomyPublication → Prop
  | .plain common taxonomy _ conceptCount _ _ =>
      ∀ sub sup : Fin common.projection.concepts.length,
        Fin.cast conceptCount sub ∈ taxonomy.target.named →
        Fin.cast conceptCount sup ∈ taxonomy.target.named →
        ((Fin.cast conceptCount sub, Fin.cast conceptCount sup) ∈
            taxonomy.semantic.subsumptions ↔ common.CommonEntails sub sup)
  | .mixed common taxonomy _ conceptCount _ _ =>
      ∀ sub sup : Fin common.projection.concepts.length,
        Fin.cast conceptCount sub ∈ taxonomy.target.named →
        Fin.cast conceptCount sup ∈ taxonomy.target.named →
        ((Fin.cast conceptCount sub, Fin.cast conceptCount sup) ∈
            taxonomy.semantic.subsumptions ↔ common.CommonEntails sub sup)

theorem target_entails_source_iff
    (target : List (Hypertableau.Clause
      (Fin targetVars) (Fin targetConcepts) (Fin targetRoles)))
    (source : List
      (Hypertableau.Clause (Fin nvars) (Fin concepts) (Fin roles)))
    (hc : targetConcepts = concepts)
    (hexact : mapOntology target = mapOntology source)
    (sub sup : Fin targetConcepts) :
    EntailsSub target sub sup ↔
      EntailsSub source (Fin.cast hc sub) (Fin.cast hc sup) := by
  rw [← entails_mapOntology_finite_iff target sub sup]
  rw [← entails_mapOntology_finite_iff source (Fin.cast hc sub) (Fin.cast hc sup)]
  simpa using congrArg
    (fun ontology => EntailsSub ontology sub.val sup.val) hexact

theorem DecodedMixedTaxonomyPublication.common_semantics
    (decoded : DecodedMixedTaxonomyPublication) : decoded.CommonSemantics := by
  cases decoded with
  | plain common taxonomy hv hc hr hexact =>
      intro sub sup hsub hsup
      rw [taxonomy.subsumptions_exact _ _ hsub hsup]
      rw [← target_entails_source_iff common.projection.target
        taxonomy.normalization.source hc hexact]
      exact (common.entails_target_iff sub sup).symm
  | mixed common taxonomy hv hc hr hexact =>
      intro sub sup hsub hsup
      rw [taxonomy.subsumptions_exact _ _ hsub hsup]
      rw [← target_entails_source_iff common.projection.target
        taxonomy.normalization.source hc hexact]
      exact (common.entails_target_iff sub sup).symm

def WireMixedTaxonomyPublication.SemanticallyValid
    (wire : WireMixedTaxonomyPublication) : Prop :=
  wire.document.runs.check = true ∧
    wire.document.payloadBoundB = true ∧
    ∃ decoded : DecodedMixedTaxonomyPublication,
      wire.decode = .ok decoded ∧ decoded.CommonSemantics

theorem WireMixedTaxonomyPublication.check_sound
    (wire : WireMixedTaxonomyPublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  have hdecodeOk : ∃ decoded, wire.decode = .ok decoded := by
    cases hdecode : wire.decode with
    | error message => simp [WireMixedTaxonomyPublication.check, hdecode] at hcheck
    | ok decoded => exact ⟨decoded, rfl⟩
  rcases hdecodeOk with ⟨decoded, hdecode⟩
  have hdocument : wire.document.check = true := by
    by_contra hfalse
    by_cases hversion : wire.version = 1 <;>
      simp [WireMixedTaxonomyPublication.decode, hversion, hfalse] at hdecode
  have hsourceBound := wire.document.check_sound hdocument
  exact ⟨hsourceBound.2.1, hsourceBound.2.2.1, decoded,
    hdecode, decoded.common_semantics⟩

#print axioms DecodedMixedTaxonomyPublication.common_semantics
#print axioms WireMixedTaxonomyPublication.check_sound

end ContextCalculus.HTMixedTaxonomyCommonPublication
