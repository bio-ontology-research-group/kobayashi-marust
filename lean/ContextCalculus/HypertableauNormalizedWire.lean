import ContextCalculus.HypertableauEqualityNormalizationWire
import ContextCalculus.HypertableauEqualityWire
import ContextCalculus.HypertableauCardinalityWire
import ContextCalculus.HypertableauPreprocessingWire
import ContextCalculus.HypertableauRegularDecisionWire

/-!
# Source-aware hypertableau certificate wire

Version 3 wraps an unchanged version-1 or version-2 HT certificate with one
checked equality-premise normalization record per target clause. Acceptance
therefore establishes the evidence result for the supplied source ontology,
not merely for Rust's normalized internal clause list.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireNormalizedPayload where
  | plain (certificate : WireCertificate)
  | equality (certificate : WireEqCertificate)
  | cardinality (certificate : WireCardinalityEqCertificate)
  | regular (certificate : WireRegularDecisionCertificate)
deriving FromJson, ToJson, Repr

structure WireNormalizedCertificate where
  version : Nat
  normalization : List WireClauseNormalization
  preprocessing : Option WirePreprocessingEvidence := none
  payload : WireNormalizedPayload
deriving FromJson, ToJson, Repr

def DecodedEvidence.base : DecodedEvidence → DecodedCertificate
  | .sat decoded | .unsat decoded _ | .subsumption decoded _ _ _ _ |
      .unsatisfiableConcept decoded _ _ _ | .nonSubsumption decoded _ _ _ |
      .satisfiableConcept decoded _ _ => decoded

def DecodedEqCertificate.ontology (decoded : DecodedEqCertificate) :
    List (Clause (Fin decoded.variableCount) (Fin decoded.conceptCount)
      (Fin decoded.roleCount)) :=
  match decoded.evidence with
  | .sat certificate | .unsat certificate _ | .subsumption certificate _ _ _ _ |
      .unsatisfiableConcept certificate _ _ _ | .nonSubsumption certificate _ _ _ |
      .satisfiableConcept certificate _ _ => certificate.base.ontology

structure DecodedModelNormalization
    (target : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) where
  source : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  equivalent : ModelEquivalent source target

structure DecodedNormalizedPlain where
  evidence : DecodedEvidence
  normalization : DecodedModelNormalization evidence.base.certificate.ontology

structure DecodedNormalizedEquality where
  evidence : DecodedEqCertificate
  normalization : DecodedModelNormalization evidence.ontology

def DecodedCardinalityEqCertificate.ontology
    (decoded : DecodedCardinalityEqCertificate) :=
  decoded.base.rootCertificate.base.ontology

structure DecodedNormalizedCardinality where
  evidence : DecodedCardinalityEqCertificate
  normalization : DecodedModelNormalization evidence.ontology

def DecodedRegularDecision.variableCount : DecodedRegularDecision → Nat
  | .regularSat decoded => decoded.variableCount
  | .finiteUnsat decoded _ => decoded.variableCount

def DecodedRegularDecision.conceptCount : DecodedRegularDecision → Nat
  | .regularSat decoded => decoded.conceptCount
  | .finiteUnsat decoded _ => decoded.conceptCount

def DecodedRegularDecision.roleCount : DecodedRegularDecision → Nat
  | .regularSat decoded => decoded.roleCount
  | .finiteUnsat decoded _ => decoded.roleCount

def DecodedRegularDecision.ontology (decoded : DecodedRegularDecision) :
    List (Clause (Fin decoded.variableCount) (Fin decoded.conceptCount)
      (Fin decoded.roleCount)) :=
  match decoded with
  | .regularSat regular => regular.certificate.ontology
  | .finiteUnsat finite _ => finite.certificate.ontology

structure DecodedNormalizedRegular where
  evidence : DecodedRegularDecision
  normalization : DecodedModelNormalization evidence.ontology

inductive DecodedNormalizedCertificate where
  | plain (decoded : DecodedNormalizedPlain)
  | equality (decoded : DecodedNormalizedEquality)
  | cardinality (decoded : DecodedNormalizedCardinality)
  | regular (decoded : DecodedNormalizedRegular)

def WireNormalizedCertificate.decode (wire : WireNormalizedCertificate) :
    Except String DecodedNormalizedCertificate := do
  if wire.version != 3 && wire.version != 4 then
    throw s!"unsupported normalized hypertableau certificate version {wire.version}"
  match wire.payload with
  | .plain certificate =>
      let evidence ← certificate.decode
      let base := evidence.base
      let normalization : DecodedModelNormalization base.certificate.ontology ←
        if wire.version = 3 then
          let decoded ← decodeOntologyNormalization base.variableCount base.conceptCount
            base.roleCount wire.normalization base.certificate.ontology
          pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
        else
          match wire.preprocessing with
          | none => throw "version-4 HT certificate has no preprocessing evidence"
          | some preprocessing =>
              let decoded ← preprocessing.decode base.variableCount base.conceptCount
                base.roleCount wire.normalization base.certificate.ontology
              pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
      return .plain ⟨evidence, normalization⟩
  | .equality certificate =>
      let evidence ← certificate.decode
      let normalization : DecodedModelNormalization evidence.ontology ←
        if wire.version = 3 then
          let decoded ← decodeOntologyNormalization evidence.variableCount
            evidence.conceptCount evidence.roleCount wire.normalization evidence.ontology
          pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
        else
          match wire.preprocessing with
          | none => throw "version-4 HT certificate has no preprocessing evidence"
          | some preprocessing =>
              let decoded ← preprocessing.decode evidence.variableCount
                evidence.conceptCount evidence.roleCount wire.normalization evidence.ontology
              pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
      return .equality ⟨evidence, normalization⟩
  | .cardinality certificate =>
      let evidence ← certificate.decode
      let normalization : DecodedModelNormalization evidence.ontology ←
        if wire.version = 3 then
          let decoded ← decodeOntologyNormalization evidence.base.variableCount
            evidence.base.conceptCount evidence.base.roleCount wire.normalization evidence.ontology
          pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
        else
          match wire.preprocessing with
          | none => throw "version-4 HT certificate has no preprocessing evidence"
          | some preprocessing =>
              let decoded ← preprocessing.decode evidence.base.variableCount
                evidence.base.conceptCount evidence.base.roleCount wire.normalization
                evidence.ontology
              pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
      return .cardinality ⟨evidence, normalization⟩
  | .regular certificate =>
      let evidence ← certificate.decode
      let normalization : DecodedModelNormalization evidence.ontology ←
        if wire.version = 3 then
          let decoded ← decodeOntologyNormalization evidence.variableCount
            evidence.conceptCount evidence.roleCount wire.normalization evidence.ontology
          pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
        else
          match wire.preprocessing with
          | none => throw "version-4 HT certificate has no preprocessing evidence"
          | some preprocessing =>
              let decoded ← preprocessing.decode evidence.variableCount
                evidence.conceptCount evidence.roleCount wire.normalization evidence.ontology
              pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
      return .regular ⟨evidence, normalization⟩

def DecodedNormalizedCertificate.check : DecodedNormalizedCertificate → Bool
  | .plain decoded => decoded.evidence.check
  | .equality decoded => decoded.evidence.check
  | .cardinality decoded => decoded.evidence.check
  | .regular decoded => decoded.evidence.check

def WireNormalizedCertificate.check (wire : WireNormalizedCertificate) : Except String Bool := do
  return (← wire.decode).check

def DecodedNormalizedPlain.SemanticallyValid (decoded : DecodedNormalizedPlain) : Prop :=
  match decoded with
  | ⟨.sat base, normalization⟩ =>
      ∃ (Domain : Type) (I : Interp Domain (Fin base.conceptCount) (Fin base.roleCount)),
        Nonempty Domain ∧ I.models normalization.source
  | ⟨.unsat base _, normalization⟩ =>
      ¬∃ (Domain : Type) (I : Interp Domain (Fin base.conceptCount) (Fin base.roleCount)),
        Nonempty Domain ∧ I.models normalization.source
  | ⟨.subsumption _ _ sub sup _, normalization⟩ =>
      EntailsSub normalization.source sub sup
  | ⟨.unsatisfiableConcept _ _ concept _, normalization⟩ =>
      UnsatisfiableConcept normalization.source concept
  | ⟨.nonSubsumption _ _ sub sup, normalization⟩ =>
      ¬EntailsSub normalization.source sub sup
  | ⟨.satisfiableConcept _ _ concept, normalization⟩ =>
      ¬UnsatisfiableConcept normalization.source concept

theorem DecodedNormalizedPlain.check_sound (decoded : DecodedNormalizedPlain)
    (hcheck : decoded.evidence.check = true) : decoded.SemanticallyValid := by
  rcases decoded with ⟨evidence, normalization⟩
  cases evidence with
  | sat base =>
      have htarget := DecodedEvidence.check_sound (.sat base) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      rcases htarget with ⟨Domain, I, hdomain, hmodels⟩
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        normalization.equivalent
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr hmodels⟩
  | unsat base tree =>
      have htarget := DecodedEvidence.check_sound (.unsat base tree) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        normalization.equivalent
      rintro ⟨Domain, I, hdomain, hmodels⟩
      exact htarget ⟨Domain, I, hdomain, (equivalent Domain I).mp hmodels⟩
  | subsumption base root sub sup tree =>
      have htarget := DecodedEvidence.check_sound (.subsumption base root sub sup tree) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        normalization.equivalent
      exact (equivalent.entailsSub_iff sub sup).mpr htarget
  | unsatisfiableConcept base root concept tree =>
      have htarget := DecodedEvidence.check_sound
        (.unsatisfiableConcept base root concept tree) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        normalization.equivalent
      exact (equivalent.unsatisfiableConcept_iff concept).mpr htarget
  | nonSubsumption base root sub sup =>
      have htarget := DecodedEvidence.check_sound (.nonSubsumption base root sub sup) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        normalization.equivalent
      intro hsource
      exact htarget ((equivalent.entailsSub_iff sub sup).mp hsource)
  | satisfiableConcept base root concept =>
      have htarget := DecodedEvidence.check_sound (.satisfiableConcept base root concept) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        normalization.equivalent
      intro hsource
      exact htarget ((equivalent.unsatisfiableConcept_iff concept).mp hsource)

def DecodedNormalizedEquality.SemanticallyValid
    (decoded : DecodedNormalizedEquality) : Prop :=
  match decoded with
  | ⟨⟨_, conceptCount, roleCount, _, .sat _⟩, normalization⟩ =>
      ∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
        Nonempty Domain ∧ I.models normalization.source
  | ⟨⟨_, conceptCount, roleCount, _, .unsat _ _⟩, normalization⟩ =>
      ¬∃ (Domain : Type) (I : Interp Domain (Fin conceptCount) (Fin roleCount)),
        Nonempty Domain ∧ I.models normalization.source
  | ⟨⟨_, _, _, _, .subsumption _ _ sub sup _⟩, normalization⟩ =>
      EntailsSub normalization.source sub sup
  | ⟨⟨_, _, _, _, .unsatisfiableConcept _ _ concept _⟩, normalization⟩ =>
      UnsatisfiableConcept normalization.source concept
  | ⟨⟨_, _, _, _, .nonSubsumption _ _ sub sup⟩, normalization⟩ =>
      ¬EntailsSub normalization.source sub sup
  | ⟨⟨_, _, _, _, .satisfiableConcept _ _ concept⟩, normalization⟩ =>
      ¬UnsatisfiableConcept normalization.source concept

theorem DecodedNormalizedEquality.check_sound (decoded : DecodedNormalizedEquality)
    (hcheck : decoded.evidence.check = true) : decoded.SemanticallyValid := by
  rcases decoded with ⟨⟨nodeCount, conceptCount, roleCount, variableCount, evidence⟩,
    normalization⟩
  cases evidence with
  | sat certificate =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount, .sat certificate⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      rcases htarget with ⟨Domain, I, hdomain, hmodels⟩
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        normalization.equivalent
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr hmodels⟩
  | unsat certificate tree =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount, .unsat certificate tree⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        normalization.equivalent
      rintro ⟨Domain, I, hdomain, hmodels⟩
      exact htarget ⟨Domain, I, hdomain, (equivalent Domain I).mp hmodels⟩
  | subsumption certificate root sub sup tree =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .subsumption certificate root sub sup tree⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        normalization.equivalent
      exact (equivalent.entailsSub_iff sub sup).mpr htarget
  | unsatisfiableConcept certificate root concept tree =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .unsatisfiableConcept certificate root concept tree⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        normalization.equivalent
      exact (equivalent.unsatisfiableConcept_iff concept).mpr htarget
  | nonSubsumption certificate root sub sup =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .nonSubsumption certificate root sub sup⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        normalization.equivalent
      intro hsource
      exact htarget ((equivalent.entailsSub_iff sub sup).mp hsource)
  | satisfiableConcept certificate root concept =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .satisfiableConcept certificate root concept⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        normalization.equivalent
      intro hsource
      exact htarget ((equivalent.unsatisfiableConcept_iff concept).mp hsource)

def DecodedNormalizedCardinality.SemanticallyValid
    (decoded : DecodedNormalizedCardinality) : Prop :=
  match decoded.evidence.base.evidence with
  | .sat _ =>
      ∃ (Domain : Type) (I : Interp Domain (Fin decoded.evidence.base.conceptCount)
          (Fin decoded.evidence.base.roleCount)), Nonempty Domain ∧
        I.models decoded.normalization.source ∧
        I.modelsCardinalityDefs decoded.evidence.definitions
  | .unsat _ _ =>
      ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.evidence.base.conceptCount)
          (Fin decoded.evidence.base.roleCount)), Nonempty Domain ∧
        I.models decoded.normalization.source ∧
        I.modelsCardinalityDefs decoded.evidence.definitions
  | .subsumption _ _ sub sup _ =>
      EntailsSubWithCardinality decoded.normalization.source
        decoded.evidence.definitions sub sup
  | .unsatisfiableConcept _ _ concept _ =>
      UnsatisfiableConceptWithCardinality decoded.normalization.source
        decoded.evidence.definitions concept
  | .nonSubsumption _ _ sub sup =>
      ¬EntailsSubWithCardinality decoded.normalization.source
        decoded.evidence.definitions sub sup
  | .satisfiableConcept _ _ concept =>
      ¬UnsatisfiableConceptWithCardinality decoded.normalization.source
        decoded.evidence.definitions concept

theorem DecodedNormalizedCardinality.check_sound
    (decoded : DecodedNormalizedCardinality)
    (hcheck : decoded.evidence.check = true) : decoded.SemanticallyValid := by
  have htarget := decoded.evidence.check_sound hcheck
  cases hevidence : decoded.evidence.base.evidence with
  | sat certificate =>
      simp only [DecodedNormalizedCardinality.SemanticallyValid, hevidence]
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence] at htarget
      have equivalent := decoded.normalization.equivalent
      have hontology : decoded.evidence.ontology = certificate.base.ontology := by
        simp [DecodedCardinalityEqCertificate.ontology,
          DecodedEqCertificate.rootCertificate, hevidence]
      rcases htarget with ⟨Domain, I, hdomain, hmodels, hdefinitions⟩
      have hmodels' : I.models decoded.evidence.ontology := by
        simpa only [hontology] using hmodels
      exact ⟨Domain, I, hdomain,
        (equivalent Domain I).mpr hmodels', hdefinitions⟩
  | unsat certificate tree =>
      simp only [DecodedNormalizedCardinality.SemanticallyValid, hevidence]
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence] at htarget
      have equivalent := decoded.normalization.equivalent
      have hontology : decoded.evidence.ontology = certificate.base.ontology := by
        simp [DecodedCardinalityEqCertificate.ontology,
          DecodedEqCertificate.rootCertificate, hevidence]
      rintro ⟨Domain, I, hdomain, hmodels, hdefinitions⟩
      have hmodels' : I.models certificate.base.ontology := by
        simpa only [hontology] using (equivalent Domain I).mp hmodels
      exact htarget ⟨Domain, I, hdomain, hmodels', hdefinitions⟩
  | subsumption certificate root sub sup tree =>
      simp only [DecodedNormalizedCardinality.SemanticallyValid, hevidence]
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence] at htarget
      have equivalent := decoded.normalization.equivalent
      have hontology : decoded.evidence.ontology = certificate.base.ontology := by
        simp [DecodedCardinalityEqCertificate.ontology,
          DecodedEqCertificate.rootCertificate, hevidence]
      intro Domain I hmodels hdefinitions value hsub
      have hmodels' : I.models certificate.base.ontology := by
        simpa only [hontology] using (equivalent Domain I).mp hmodels
      exact htarget Domain I
        hmodels'
        hdefinitions value hsub
  | unsatisfiableConcept certificate root concept tree =>
      simp only [DecodedNormalizedCardinality.SemanticallyValid, hevidence]
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence] at htarget
      have equivalent := decoded.normalization.equivalent
      have hontology : decoded.evidence.ontology = certificate.base.ontology := by
        simp [DecodedCardinalityEqCertificate.ontology,
          DecodedEqCertificate.rootCertificate, hevidence]
      intro Domain I hmodels hdefinitions value hconcept
      have hmodels' : I.models certificate.base.ontology := by
        simpa only [hontology] using (equivalent Domain I).mp hmodels
      exact htarget Domain I
        hmodels'
        hdefinitions value hconcept
  | nonSubsumption certificate root sub sup =>
      simp only [DecodedNormalizedCardinality.SemanticallyValid, hevidence]
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence] at htarget
      have equivalent := decoded.normalization.equivalent
      have hontology : decoded.evidence.ontology = certificate.base.ontology := by
        simp [DecodedCardinalityEqCertificate.ontology,
          DecodedEqCertificate.rootCertificate, hevidence]
      intro hsource
      apply htarget
      intro Domain I hmodels hdefinitions value hsub
      have hmodels' : I.models decoded.evidence.ontology := by
        simpa only [hontology] using hmodels
      exact hsource Domain I
        ((equivalent Domain I).mpr hmodels')
        hdefinitions value hsub
  | satisfiableConcept certificate root concept =>
      simp only [DecodedNormalizedCardinality.SemanticallyValid, hevidence]
      simp only [DecodedCardinalityEqCertificate.SemanticallyValid, hevidence] at htarget
      have equivalent := decoded.normalization.equivalent
      have hontology : decoded.evidence.ontology = certificate.base.ontology := by
        simp [DecodedCardinalityEqCertificate.ontology,
          DecodedEqCertificate.rootCertificate, hevidence]
      intro hsource
      apply htarget
      intro Domain I hmodels hdefinitions value hconcept
      have hmodels' : I.models decoded.evidence.ontology := by
        simpa only [hontology] using hmodels
      exact hsource Domain I
        ((equivalent Domain I).mpr hmodels')
        hdefinitions value hconcept

def DecodedNormalizedRegular.SemanticallyValid
    (decoded : DecodedNormalizedRegular) : Prop :=
  match decoded.evidence with
  | .regularSat _ =>
      ∃ (Domain : Type)
        (I : Interp Domain (Fin decoded.evidence.conceptCount)
          (Fin decoded.evidence.roleCount)),
        Nonempty Domain ∧ I.models decoded.normalization.source
  | .finiteUnsat _ _ =>
      ¬∃ (Domain : Type)
        (I : Interp Domain (Fin decoded.evidence.conceptCount)
          (Fin decoded.evidence.roleCount)),
        Nonempty Domain ∧ I.models decoded.normalization.source

theorem DecodedNormalizedRegular.check_sound
    (decoded : DecodedNormalizedRegular)
    (hcheck : decoded.evidence.check = true) : decoded.SemanticallyValid := by
  rcases decoded with ⟨evidence, normalization⟩
  have htarget := evidence.check_sound hcheck
  cases evidence with
  | regularSat regular =>
      simp only [DecodedNormalizedRegular.SemanticallyValid]
      simp only [DecodedRegularDecision.SemanticallyCorrect] at htarget
      rcases htarget with ⟨Domain, I, hdomain, hmodels⟩
      exact ⟨Domain, I, hdomain,
        (normalization.equivalent Domain I).mpr hmodels⟩
  | finiteUnsat finite tree =>
      simp only [DecodedNormalizedRegular.SemanticallyValid]
      simp only [DecodedRegularDecision.SemanticallyCorrect] at htarget
      rintro ⟨Domain, I, hdomain, hmodels⟩
      exact htarget ⟨Domain, I, hdomain,
        (normalization.equivalent Domain I).mp hmodels⟩

def DecodedNormalizedCertificate.SemanticallyValid :
    DecodedNormalizedCertificate → Prop
  | .plain decoded => decoded.SemanticallyValid
  | .equality decoded => decoded.SemanticallyValid
  | .cardinality decoded => decoded.SemanticallyValid
  | .regular decoded => decoded.SemanticallyValid

theorem DecodedNormalizedCertificate.check_sound
    (decoded : DecodedNormalizedCertificate) (hcheck : decoded.check = true) :
    decoded.SemanticallyValid := by
  cases decoded with
  | plain decoded => exact decoded.check_sound hcheck
  | equality decoded => exact decoded.check_sound hcheck
  | cardinality decoded => exact decoded.check_sound hcheck
  | regular decoded => exact decoded.check_sound hcheck

#print axioms DecodedNormalizedPlain.check_sound
#print axioms DecodedNormalizedEquality.check_sound
#print axioms DecodedNormalizedCardinality.check_sound
#print axioms DecodedNormalizedRegular.check_sound
#print axioms DecodedNormalizedCertificate.check_sound

namespace Tests

private def normalizedContradiction : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 0
  role_count := 0
  variable_count := 2
  ontology := [{ body := [], head := [] }]
  labels := []
  edges := []
  obligations := []
  evidence := .unsat (.branch 0 [0, 0] [])

private def sourceNormalization : WireClauseNormalization where
  source := { body := [.eq 0 1], head := [] }
  representatives := [0, 0]
  representative_paths := [[0], [1, 0]]

private def validDocument : WireNormalizedCertificate where
  version := 3
  normalization := [sourceNormalization]
  payload := .plain normalizedContradiction

example : validDocument.check = .ok true := by native_decide

private def invalidPathDocument : WireNormalizedCertificate :=
  { validDocument with normalization := [
      { sourceNormalization with representative_paths := [[0], [1]] }] }

private def rejected : Except String Bool → Bool
  | .error _ => true
  | .ok _ => false

example : rejected invalidPathDocument.check = true := by native_decide

private def wrongSourceDocument : WireNormalizedCertificate :=
  { validDocument with normalization := [
      { sourceNormalization with source := { body := [], head := [] } }] }

example : rejected wrongSourceDocument.check = true := by native_decide

private def absorbedClash : WireClause where
  body := [
    .concept { concept := 0, neg := false } 0,
    .concept { concept := 1, neg := false } 0]
  head := []

private def triggerSource : WireClause where
  body := []
  head := [
    .concept { concept := 0, neg := true } 0,
    .concept { concept := 1, neg := true } 0]

private def preprocessedContradiction : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 2
  role_count := 0
  variable_count := 1
  ontology := [absorbedClash]
  labels := []
  edges := []
  obligations := []
  evidence := .sat

private def identityClashNormalization : WireClauseNormalization where
  source := absorbedClash
  representatives := [0]
  representative_paths := [[0]]

private def triggerPreprocessing : WirePreprocessingEvidence where
  source := [triggerSource]
  absorbed := [absorbedClash]
  trigger_steps := [.absorb 0 [0, 1] []]
  contrapositives := []

private def validPreprocessedDocument : WireNormalizedCertificate where
  version := 4
  normalization := [identityClashNormalization]
  preprocessing := some triggerPreprocessing
  payload := .plain preprocessedContradiction

example : validPreprocessedDocument.check = .ok true := by native_decide

private def missingPreprocessingDocument : WireNormalizedCertificate :=
  { validPreprocessedDocument with preprocessing := none }

example : rejected missingPreprocessingDocument.check = true := by native_decide

private def forgedPreprocessingDocument : WireNormalizedCertificate :=
  { validPreprocessedDocument with preprocessing := some {
      triggerPreprocessing with trigger_steps := [.absorb 0 [0] [1]] } }

example : rejected forgedPreprocessingDocument.check = true := by native_decide

private def normalizedRegularSat : WireRegularCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 0
  variable_count := 1
  labels := []
  edges := []
  obligations := []
  redirect := [0]
  cover := []
  sub_roles := []
  inverse_roles := []
  chains := []
  reflexive_roles := []
  role_clauses := []
  residual := []

private def regularDecision : WireRegularDecisionCertificate where
  version := 1
  evidence := .regular_sat normalizedRegularSat

private def normalizedRegularDocument : WireNormalizedCertificate where
  version := 3
  normalization := []
  payload := .regular regularDecision

example : normalizedRegularDocument.check = .ok true := by native_decide

end Tests

end ContextCalculus.Hypertableau
