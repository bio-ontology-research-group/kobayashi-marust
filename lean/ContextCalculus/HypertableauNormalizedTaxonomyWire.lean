import ContextCalculus.HypertableauEqualityNormalizationWire
import ContextCalculus.HypertableauMixedTaxonomyWire
import ContextCalculus.HypertableauNormalizedWire

/-!
# Source-aware complete hypertableau taxonomy certificates

Version 3 wraps an unchanged version-1 or mixed version-2 complete taxonomy
with checked equality-premise normalization evidence. The decoded semantic
taxonomy is transferred cell by cell from the normalized target ontology to
the supplied source ontology.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireNormalizedTaxonomyPayload where
  | plain (certificate : WireTaxonomyCertificate)
  | mixed (certificate : WireMixedTaxonomyCertificate)
deriving FromJson, ToJson, Repr

structure WireNormalizedTaxonomyCertificate where
  version : Nat
  normalization : List WireClauseNormalization
  preprocessing : Option WirePreprocessingEvidence := none
  payload : WireNormalizedTaxonomyPayload
deriving FromJson, ToJson, Repr

def ConceptDecision.transfer
    (equivalent : ModelEquivalent source target) :
    ConceptDecision target concept → ConceptDecision source concept
  | .unsatisfiable proof =>
      .unsatisfiable ((equivalent.unsatisfiableConcept_iff concept).mpr proof)
  | .satisfiable counterexample => .satisfiable fun proof =>
      counterexample ((equivalent.unsatisfiableConcept_iff concept).mp proof)

def SubsumptionDecision.transfer
    (equivalent : ModelEquivalent source target) :
    SubsumptionDecision target sub sup → SubsumptionDecision source sub sup
  | .entailed proof => .entailed ((equivalent.entailsSub_iff sub sup).mpr proof)
  | .notEntailed counterexample => .notEntailed fun proof =>
      counterexample ((equivalent.entailsSub_iff sub sup).mp proof)

def CompleteTaxonomyCertificate.transfer
    (equivalent : ModelEquivalent source target)
    (certificate : CompleteTaxonomyCertificate target named) :
    CompleteTaxonomyCertificate source named where
  concept candidate hnamed :=
    (certificate.concept candidate hnamed).transfer equivalent
  subsumption sub hsub sup hsup :=
    (certificate.subsumption sub hsub sup hsup).transfer equivalent

structure DecodedNormalizedPlainTaxonomy where
  target : DecodedTaxonomyCertificate
  normalization : DecodedModelNormalization target.ontology

structure DecodedNormalizedMixedTaxonomy where
  target : DecodedMixedTaxonomyCertificate
  normalization : DecodedModelNormalization target.ontology

inductive DecodedNormalizedTaxonomyCertificate where
  | plain (decoded : DecodedNormalizedPlainTaxonomy)
  | mixed (decoded : DecodedNormalizedMixedTaxonomy)

def WireNormalizedTaxonomyCertificate.decode
    (wire : WireNormalizedTaxonomyCertificate) :
    Except String DecodedNormalizedTaxonomyCertificate := do
  if wire.version != 3 && wire.version != 4 then
    throw s!"unsupported normalized hypertableau taxonomy certificate version {wire.version}"
  match wire.payload with
  | .plain certificate =>
      let target ← certificate.decode
      let normalization : DecodedModelNormalization target.ontology ←
        if wire.version = 3 then
          let decoded ← decodeOntologyNormalization target.variableCount
            target.conceptCount target.roleCount wire.normalization target.ontology
          pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
        else
          match wire.preprocessing with
          | none => throw "version-4 HT taxonomy has no preprocessing evidence"
          | some preprocessing =>
              let decoded ← preprocessing.decode target.variableCount target.conceptCount
                target.roleCount wire.normalization target.ontology
              pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
      return .plain ⟨target, normalization⟩
  | .mixed certificate =>
      let target ← certificate.decode
      let normalization : DecodedModelNormalization target.ontology ←
        if wire.version = 3 then
          let decoded ← decodeOntologyNormalization target.variableCount
            target.conceptCount target.roleCount wire.normalization target.ontology
          pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
        else
          match wire.preprocessing with
          | none => throw "version-4 HT taxonomy has no preprocessing evidence"
          | some preprocessing =>
              let decoded ← preprocessing.decode target.variableCount target.conceptCount
                target.roleCount wire.normalization target.ontology
              pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
      return .mixed ⟨target, normalization⟩

def WireNormalizedTaxonomyCertificate.check
    (wire : WireNormalizedTaxonomyCertificate) : Bool :=
  wire.decode.isOk

def DecodedNormalizedPlainTaxonomy.semantic
    (decoded : DecodedNormalizedPlainTaxonomy) :
    CompleteTaxonomyCertificate decoded.normalization.source decoded.target.named :=
  decoded.target.semantic.transfer decoded.normalization.equivalent

def DecodedNormalizedMixedTaxonomy.semantic
    (decoded : DecodedNormalizedMixedTaxonomy) :
    CompleteTaxonomyCertificate decoded.normalization.source decoded.target.named :=
  decoded.target.semantic.transfer decoded.normalization.equivalent

def DecodedNormalizedTaxonomyCertificate.SemanticallyComplete :
    DecodedNormalizedTaxonomyCertificate → Prop
  | .plain decoded =>
      ∃ certificate : CompleteTaxonomyCertificate decoded.normalization.source
        decoded.target.named, certificate = decoded.semantic
  | .mixed decoded =>
      ∃ certificate : CompleteTaxonomyCertificate decoded.normalization.source
        decoded.target.named, certificate = decoded.semantic

theorem DecodedNormalizedTaxonomyCertificate.check_sound
    (decoded : DecodedNormalizedTaxonomyCertificate) : decoded.SemanticallyComplete := by
  cases decoded with
  | plain decoded => exact ⟨decoded.semantic, rfl⟩
  | mixed decoded => exact ⟨decoded.semantic, rfl⟩

theorem DecodedNormalizedPlainTaxonomy.unsatisfiable_exact
    (decoded : DecodedNormalizedPlainTaxonomy)
    (concept : Fin decoded.target.conceptCount)
    (hnamed : concept ∈ decoded.target.named) :
    concept ∈ decoded.semantic.unsatisfiable ↔
      UnsatisfiableConcept decoded.normalization.source concept :=
  decoded.semantic.unsatisfiable_exact concept hnamed

theorem DecodedNormalizedPlainTaxonomy.subsumptions_exact
    (decoded : DecodedNormalizedPlainTaxonomy)
    (sub sup : Fin decoded.target.conceptCount)
    (hsub : sub ∈ decoded.target.named) (hsup : sup ∈ decoded.target.named) :
    (sub, sup) ∈ decoded.semantic.subsumptions ↔
      EntailsSub decoded.normalization.source sub sup :=
  decoded.semantic.subsumptions_exact sub sup hsub hsup

theorem DecodedNormalizedMixedTaxonomy.unsatisfiable_exact
    (decoded : DecodedNormalizedMixedTaxonomy)
    (concept : Fin decoded.target.conceptCount)
    (hnamed : concept ∈ decoded.target.named) :
    concept ∈ decoded.semantic.unsatisfiable ↔
      UnsatisfiableConcept decoded.normalization.source concept :=
  decoded.semantic.unsatisfiable_exact concept hnamed

theorem DecodedNormalizedMixedTaxonomy.subsumptions_exact
    (decoded : DecodedNormalizedMixedTaxonomy)
    (sub sup : Fin decoded.target.conceptCount)
    (hsub : sub ∈ decoded.target.named) (hsup : sup ∈ decoded.target.named) :
    (sub, sup) ∈ decoded.semantic.subsumptions ↔
      EntailsSub decoded.normalization.source sub sup :=
  decoded.semantic.subsumptions_exact sub sup hsub hsup

namespace NormalizedTaxonomyWireTests

private def conceptClashPayload : WireQueryPayload where
  node_count := 1
  labels := [{ node := 0, literal := ⟨0, false⟩ }]
  edges := []
  obligations := []
  evidence := .unsatisfiable_concept 0 0 (.branch 0 [0, 0] [])

private def subsumptionClashPayload : WireQueryPayload where
  node_count := 1
  labels := [
    { node := 0, literal := ⟨0, false⟩ },
    { node := 0, literal := ⟨0, true⟩ }]
  edges := []
  obligations := []
  evidence := .subsumption 0 0 0 (.branch 0 [0, 0] [])

private def targetTaxonomy : WireTaxonomyCertificate where
  version := 1
  concept_count := 1
  role_count := 0
  variable_count := 2
  ontology := [{ body := [], head := [] }]
  named := [0]
  concepts := [conceptClashPayload]
  subsumptions := [[subsumptionClashPayload]]

private def sourceNormalization : WireClauseNormalization where
  source := { body := [.eq 0 1], head := [] }
  representatives := [0, 0]
  representative_paths := [[0], [1, 0]]

private def accepted : WireNormalizedTaxonomyCertificate where
  version := 3
  normalization := [sourceNormalization]
  payload := .plain targetTaxonomy

example : accepted.check = true := by native_decide

private def badPath : WireNormalizedTaxonomyCertificate :=
  { accepted with normalization := [
      { sourceNormalization with representative_paths := [[0], [1]] }] }

example : badPath.check = false := by native_decide

private def missingCell : WireNormalizedTaxonomyCertificate :=
  { accepted with payload := .plain { targetTaxonomy with subsumptions := [] } }

example : missingCell.check = false := by native_decide

end NormalizedTaxonomyWireTests

#print axioms ConceptDecision.transfer
#print axioms SubsumptionDecision.transfer
#print axioms CompleteTaxonomyCertificate.transfer
#print axioms DecodedNormalizedTaxonomyCertificate.check_sound
#print axioms DecodedNormalizedPlainTaxonomy.unsatisfiable_exact
#print axioms DecodedNormalizedPlainTaxonomy.subsumptions_exact
#print axioms DecodedNormalizedMixedTaxonomy.unsatisfiable_exact
#print axioms DecodedNormalizedMixedTaxonomy.subsumptions_exact

end ContextCalculus.Hypertableau
