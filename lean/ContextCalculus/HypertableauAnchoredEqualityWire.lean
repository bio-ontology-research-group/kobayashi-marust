import ContextCalculus.HypertableauAnchoredEqualityCertificate
import ContextCalculus.HypertableauAnchoredWire
import ContextCalculus.HypertableauEqualityWire
import Lean

/-!
# Bounded wire for equality-backed anchored HT certificates

The equality ontology and state decode independently from the regular
certificate. The semantic checker, rather than the decoder, proves that the
two ontologies coincide and that the regular state is the exact representative
image of the equality state.
-/

namespace ContextCalculus.Hypertableau

open Lean
open AnchoredForestDomain

structure WireAnchoredEqCertificate where
  version : Nat
  equality_node_count : Nat
  regular : WireRegularCertificate
  equality_ontology : List WireClause
  equality_state : WireEqState
  class_map : List Nat
  nominal_roots : List (Option Nat)
deriving FromJson, ToJson, Repr

structure DecodedAnchoredEqCertificate where
  eqNodeCount : Nat
  regularNodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  positive : 0 < regularNodeCount
  certificate : FiniteAnchoredEqCertificate
    eqNodeCount regularNodeCount conceptCount roleCount variableCount

def decodeClassMap (eqNodeCount regularNodeCount : Nat) (values : List Nat) :
    Except String (Fin eqNodeCount → Fin regularNodeCount) := do
  let decoded ← values.mapM (checkedFin "class_map target" regularNodeCount)
  if h : decoded.length = eqNodeCount then
    return fun node => decoded.get (h.symm ▸ node)
  else
    throw s!"class_map has {decoded.length} entries, expected {eqNodeCount}"

def WireAnchoredEqCertificate.decode (wire : WireAnchoredEqCertificate) :
    Except String DecodedAnchoredEqCertificate := do
  if wire.version != 1 then
    throw s!"unsupported equality-backed anchored certificate version {wire.version}"
  let regular ← wire.regular.decode
  let ontology ← wire.equality_ontology.mapM
    (WireClause.decode regular.variableCount regular.conceptCount regular.roleCount)
  let equality ← wire.equality_state.decode wire.equality_node_count regular.conceptCount
    regular.roleCount regular.variableCount ontology
  let classMap ← decodeClassMap wire.equality_node_count regular.nodeCount wire.class_map
  let nominalRoot ← decodeNominalRoots regular.nodeCount regular.conceptCount
    wire.nominal_roots
  return {
    eqNodeCount := wire.equality_node_count
    regularNodeCount := regular.nodeCount
    conceptCount := regular.conceptCount
    roleCount := regular.roleCount
    variableCount := regular.variableCount
    positive := regular.positive
    certificate := { equality, regular := regular.certificate, classMap, nominalRoot }
  }

def DecodedAnchoredEqCertificate.check
    (decoded : DecodedAnchoredEqCertificate) : Bool :=
  decoded.certificate.check

def WireAnchoredEqCertificate.check (wire : WireAnchoredEqCertificate) :
    Except String Bool := do
  return (← wire.decode).check

theorem DecodedAnchoredEqCertificate.check_models
    (decoded : DecodedAnchoredEqCertificate)
    (hcheck : decoded.check = true) :
    letI : NeZero decoded.regularNodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
    (interpretation decoded.certificate.regular.state
      decoded.certificate.regular.redirect (fun _ _ _ _ => True)
      (NominalAnchor decoded.certificate.nominalRoot)
      decoded.certificate.regular.rules decoded.certificate.nominalRoot).models
      decoded.certificate.equality.base.ontology := by
  letI : NeZero decoded.regularNodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
  exact decoded.certificate.check_models hcheck

#print axioms DecodedAnchoredEqCertificate.check_models

end ContextCalculus.Hypertableau
