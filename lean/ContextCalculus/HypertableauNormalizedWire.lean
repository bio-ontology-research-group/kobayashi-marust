import ContextCalculus.HypertableauEqualityNormalizationWire
import ContextCalculus.HypertableauEqualityWire

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
deriving FromJson, ToJson, Repr

structure WireNormalizedCertificate where
  version : Nat
  normalization : List WireClauseNormalization
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

structure DecodedNormalizedPlain where
  evidence : DecodedEvidence
  normalization : DecodedOntologyNormalization evidence.base.certificate.ontology

structure DecodedNormalizedEquality where
  evidence : DecodedEqCertificate
  normalization : DecodedOntologyNormalization evidence.ontology

inductive DecodedNormalizedCertificate where
  | plain (decoded : DecodedNormalizedPlain)
  | equality (decoded : DecodedNormalizedEquality)

def WireNormalizedCertificate.decode (wire : WireNormalizedCertificate) :
    Except String DecodedNormalizedCertificate := do
  if wire.version != 3 then
    throw s!"unsupported normalized hypertableau certificate version {wire.version}"
  match wire.payload with
  | .plain certificate =>
      let evidence ← certificate.decode
      let base := evidence.base
      let normalization ← decodeOntologyNormalization base.variableCount base.conceptCount
        base.roleCount wire.normalization base.certificate.ontology
      return .plain ⟨evidence, normalization⟩
  | .equality certificate =>
      let evidence ← certificate.decode
      let normalization ← decodeOntologyNormalization evidence.variableCount
        evidence.conceptCount evidence.roleCount wire.normalization evidence.ontology
      return .equality ⟨evidence, normalization⟩

def DecodedNormalizedCertificate.check : DecodedNormalizedCertificate → Bool
  | .plain decoded => decoded.evidence.check
  | .equality decoded => decoded.evidence.check

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
        fun Domain I => normalization.proof.models_iff I
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr hmodels⟩
  | unsat base tree =>
      have htarget := DecodedEvidence.check_sound (.unsat base tree) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        fun Domain I => normalization.proof.models_iff I
      rintro ⟨Domain, I, hdomain, hmodels⟩
      exact htarget ⟨Domain, I, hdomain, (equivalent Domain I).mp hmodels⟩
  | subsumption base root sub sup tree =>
      have htarget := DecodedEvidence.check_sound (.subsumption base root sub sup tree) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        fun Domain I => normalization.proof.models_iff I
      exact (equivalent.entailsSub_iff sub sup).mpr htarget
  | unsatisfiableConcept base root concept tree =>
      have htarget := DecodedEvidence.check_sound
        (.unsatisfiableConcept base root concept tree) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        fun Domain I => normalization.proof.models_iff I
      exact (equivalent.unsatisfiableConcept_iff concept).mpr htarget
  | nonSubsumption base root sub sup =>
      have htarget := DecodedEvidence.check_sound (.nonSubsumption base root sub sup) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        fun Domain I => normalization.proof.models_iff I
      intro hsource
      exact htarget ((equivalent.entailsSub_iff sub sup).mp hsource)
  | satisfiableConcept base root concept =>
      have htarget := DecodedEvidence.check_sound (.satisfiableConcept base root concept) hcheck
      simp only [DecodedNormalizedPlain.SemanticallyValid]
      simp only [DecodedEvidence.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source base.certificate.ontology :=
        fun Domain I => normalization.proof.models_iff I
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
        fun Domain I => normalization.proof.models_iff I
      exact ⟨Domain, I, hdomain, (equivalent Domain I).mpr hmodels⟩
  | unsat certificate tree =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount, .unsat certificate tree⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        fun Domain I => normalization.proof.models_iff I
      rintro ⟨Domain, I, hdomain, hmodels⟩
      exact htarget ⟨Domain, I, hdomain, (equivalent Domain I).mp hmodels⟩
  | subsumption certificate root sub sup tree =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .subsumption certificate root sub sup tree⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        fun Domain I => normalization.proof.models_iff I
      exact (equivalent.entailsSub_iff sub sup).mpr htarget
  | unsatisfiableConcept certificate root concept tree =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .unsatisfiableConcept certificate root concept tree⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        fun Domain I => normalization.proof.models_iff I
      exact (equivalent.unsatisfiableConcept_iff concept).mpr htarget
  | nonSubsumption certificate root sub sup =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .nonSubsumption certificate root sub sup⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        fun Domain I => normalization.proof.models_iff I
      intro hsource
      exact htarget ((equivalent.entailsSub_iff sub sup).mp hsource)
  | satisfiableConcept certificate root concept =>
      have htarget := DecodedEqCertificate.check_sound
        ⟨nodeCount, conceptCount, roleCount, variableCount,
          .satisfiableConcept certificate root concept⟩ hcheck
      simp only [DecodedNormalizedEquality.SemanticallyValid]
      simp only [DecodedEqCertificate.SemanticallyValid] at htarget
      have equivalent : ModelEquivalent normalization.source certificate.base.ontology :=
        fun Domain I => normalization.proof.models_iff I
      intro hsource
      exact htarget ((equivalent.unsatisfiableConcept_iff concept).mp hsource)

def DecodedNormalizedCertificate.SemanticallyValid :
    DecodedNormalizedCertificate → Prop
  | .plain decoded => decoded.SemanticallyValid
  | .equality decoded => decoded.SemanticallyValid

theorem DecodedNormalizedCertificate.check_sound
    (decoded : DecodedNormalizedCertificate) (hcheck : decoded.check = true) :
    decoded.SemanticallyValid := by
  cases decoded with
  | plain decoded => exact decoded.check_sound hcheck
  | equality decoded => exact decoded.check_sound hcheck

#print axioms DecodedNormalizedPlain.check_sound
#print axioms DecodedNormalizedEquality.check_sound
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

end Tests

end ContextCalculus.Hypertableau
