import ContextCalculus.HypertableauRegularWire
import ContextCalculus.HypertableauWire
import Lean

/-!
# Checked global HT decision envelope

One versioned document carries either a regular-unravelling model or an
empty-root finite refutation. The outcome tag is untrusted: decoding restricts
the finite branch to global `unsat` evidence, and the Boolean checker validates
the selected proof object. `check_sound` proves the resulting SAT or UNSAT
statement for the exact ontology inside that branch.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireRegularDecisionEvidence where
  | regular_sat (certificate : WireRegularCertificate)
  | finite_unsat (certificate : WireCertificate)
deriving FromJson, ToJson, Repr

structure WireRegularDecisionCertificate where
  version : Nat
  evidence : WireRegularDecisionEvidence
deriving FromJson, ToJson, Repr

inductive DecodedRegularDecision where
  | regularSat (decoded : DecodedRegularCertificate)
  | finiteUnsat (decoded : DecodedCertificate)
      (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
        decoded.roleCount decoded.variableCount)

def WireRegularDecisionCertificate.decode
    (wire : WireRegularDecisionCertificate) :
    Except String DecodedRegularDecision := do
  if wire.version != 1 then
    throw s!"unsupported regular HT decision version {wire.version}"
  match wire.evidence with
  | .regular_sat certificate =>
      return .regularSat (← certificate.decode)
  | .finite_unsat certificate =>
      match ← certificate.decode with
      | .unsat decoded tree => return .finiteUnsat decoded tree
      | _ => throw "finite branch of regular HT decision must contain global unsat evidence"

def DecodedRegularDecision.check : DecodedRegularDecision → Bool
  | .regularSat decoded => decoded.check
  | .finiteUnsat decoded tree => (DecodedEvidence.unsat decoded tree).check

def WireRegularDecisionCertificate.check
    (wire : WireRegularDecisionCertificate) : Except String Bool := do
  return (← wire.decode).check

def DecodedRegularDecision.SemanticallyCorrect :
    DecodedRegularDecision → Prop
  | .regularSat decoded =>
      ∃ (Domain : Type)
        (I : Interp Domain (Fin decoded.conceptCount) (Fin decoded.roleCount)),
        Nonempty Domain ∧ I.models decoded.certificate.ontology
  | .finiteUnsat decoded _ =>
      ¬∃ (Domain : Type)
        (I : Interp Domain (Fin decoded.conceptCount) (Fin decoded.roleCount)),
        Nonempty Domain ∧ I.models decoded.certificate.ontology

theorem DecodedRegularDecision.check_sound
    (decision : DecodedRegularDecision)
    (hcheck : decision.check = true) : decision.SemanticallyCorrect := by
  cases decision with
  | regularSat decoded =>
      letI : NeZero decoded.nodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
      let Domain := UnravellingDomain decoded.certificate.state
        decoded.certificate.redirect (fun _ _ _ _ => True) 0
      let I := decoded.certificate.state.regularUnravelling
        decoded.certificate.redirect (fun _ _ _ _ => True) 0
        decoded.certificate.rules
      refine ⟨Domain, I, ?_, ?_⟩
      · exact ⟨⟨0, .root⟩⟩
      · exact decoded.check_models hcheck
  | finiteUnsat decoded tree =>
      change (DecodedEvidence.unsat decoded tree).check = true at hcheck
      exact DecodedEvidence.unsat_sound decoded tree hcheck

theorem WireRegularDecisionCertificate.check_sound
    (wire : WireRegularDecisionCertificate)
    (decision : DecodedRegularDecision)
    (hdecode : wire.decode = .ok decision)
    (hcheck : wire.check = .ok true) : decision.SemanticallyCorrect := by
  simp [WireRegularDecisionCertificate.check, hdecode] at hcheck
  exact decision.check_sound hcheck

private def emptyRegular : WireRegularCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
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

private def regularSatDocument : WireRegularDecisionCertificate where
  version := 1
  evidence := .regular_sat emptyRegular

private def finiteSatPayload : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
  variable_count := 0
  ontology := []
  labels := []
  edges := []
  obligations := []
  evidence := .sat

private def wrongFiniteOutcome : WireRegularDecisionCertificate where
  version := 1
  evidence := .finite_unsat finiteSatPayload

example : regularSatDocument.check = .ok true := by native_decide
example : (match wrongFiniteOutcome.decode with
  | .error _ => true | .ok _ => false) = true := by native_decide

#print axioms DecodedRegularDecision.check_sound
#print axioms WireRegularDecisionCertificate.check_sound

end ContextCalculus.Hypertableau
