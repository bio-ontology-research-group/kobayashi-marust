import ContextCalculus.HypertableauAnchoredEqualityWire
import ContextCalculus.HypertableauNormalizedWire

/-!
# Source-aware anchored equality certificates

This wire composes the dense equality quotient and anchored-model checker with
the exact source-to-runtime normalization evidence.  It is a SAT witness only:
acceptance constructs a nonempty model of the source ontology.
-/

namespace ContextCalculus.Hypertableau

open Lean
open AnchoredForestDomain

structure WireNormalizedAnchoredEqCertificate where
  version : Nat
  normalization : Option (List WireClauseNormalization) := none
  preprocessing : Option WirePreprocessingEvidence := none
  certificate : WireAnchoredEqCertificate
deriving FromJson, ToJson, Repr

structure DecodedNormalizedAnchoredEqCertificate where
  anchored : DecodedAnchoredEqCertificate
  normalization : DecodedModelNormalization anchored.certificate.equality.base.ontology

def WireNormalizedAnchoredEqCertificate.decode
    (wire : WireNormalizedAnchoredEqCertificate) :
    Except String DecodedNormalizedAnchoredEqCertificate := do
  if wire.version != 5 then
    throw s!"unsupported normalized anchored equality certificate version {wire.version}"
  let anchored ← wire.certificate.decode
  let target := anchored.certificate.equality.base.ontology
  let normalization : DecodedModelNormalization target ←
    match wire.normalization, wire.preprocessing with
    | none, none => pure ⟨target, fun _ _ => Iff.rfl⟩
    | none, some _ =>
        throw "anchored equality preprocessing requires normalization evidence"
    | some records, none =>
        let decoded ← decodeOntologyNormalization anchored.variableCount
          anchored.conceptCount anchored.roleCount records target
        pure ⟨decoded.source, fun _ I => decoded.proof.models_iff I⟩
    | some records, some preprocessing =>
        let decoded ← preprocessing.decode anchored.variableCount
          anchored.conceptCount anchored.roleCount records target
        pure ⟨decoded.source, decoded.proof.modelEquivalent⟩
  return ⟨anchored, normalization⟩

def DecodedNormalizedAnchoredEqCertificate.check
    (decoded : DecodedNormalizedAnchoredEqCertificate) : Bool :=
  decoded.anchored.check

def WireNormalizedAnchoredEqCertificate.check
    (wire : WireNormalizedAnchoredEqCertificate) : Except String Bool := do
  return (← wire.decode).check

def DecodedNormalizedAnchoredEqCertificate.SemanticallyValid
    (decoded : DecodedNormalizedAnchoredEqCertificate) : Prop :=
  ∃ (Domain : Type)
    (I : Interp Domain (Fin decoded.anchored.conceptCount)
      (Fin decoded.anchored.roleCount)),
    Nonempty Domain ∧ I.models decoded.normalization.source

theorem DecodedNormalizedAnchoredEqCertificate.check_sound
    (decoded : DecodedNormalizedAnchoredEqCertificate)
    (hcheck : decoded.check = true) : decoded.SemanticallyValid := by
  letI : NeZero decoded.anchored.regularNodeCount :=
    ⟨Nat.ne_of_gt decoded.anchored.positive⟩
  let I := interpretation decoded.anchored.certificate.regular.state
    decoded.anchored.certificate.regular.redirect (fun _ _ _ _ => True)
    (NominalAnchor decoded.anchored.certificate.nominalRoot)
    decoded.anchored.certificate.regular.rules
    decoded.anchored.certificate.nominalRoot
  have hmodels : I.models decoded.anchored.certificate.equality.base.ontology :=
    decoded.anchored.certificate.check_models hcheck
  have hdomain : Nonempty (AnchoredForestDomain
      decoded.anchored.certificate.regular.state
      decoded.anchored.certificate.regular.redirect (fun _ _ _ _ => True)
      (NominalAnchor decoded.anchored.certificate.nominalRoot)) :=
    ⟨AnchoredForestDomain.root decoded.anchored.certificate.regular.state
      decoded.anchored.certificate.regular.redirect (fun _ _ _ _ => True)
      (NominalAnchor decoded.anchored.certificate.nominalRoot)
      ⟨0, decoded.anchored.positive⟩⟩
  exact ⟨_, I, hdomain,
    (decoded.normalization.equivalent _ I).mpr hmodels⟩

#print axioms DecodedNormalizedAnchoredEqCertificate.check_sound

end ContextCalculus.Hypertableau
