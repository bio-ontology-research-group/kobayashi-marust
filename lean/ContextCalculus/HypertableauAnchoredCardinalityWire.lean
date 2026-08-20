import ContextCalculus.HypertableauAnchoredCardinalityCertificate
import ContextCalculus.HypertableauAnchoredEqualityWire
import ContextCalculus.HypertableauRegularCardinalityWire
import Lean

/-! # Bounded wire for anchored equality and cardinality certificates -/

namespace ContextCalculus.Hypertableau

open Lean
open AnchoredForestDomain

structure WireAnchoredCardinalityEqCertificate where
  version : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  anchored : WireAnchoredEqCertificate
  slots : List WireRegularSlot
  definitions : List WireCardinalityDef
deriving FromJson, ToJson, Repr

structure DecodedAnchoredCardinalityEqCertificate where
  eqNodeCount : Nat
  regularNodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  positive : 0 < regularNodeCount
  certificate : FiniteAnchoredCardinalityEqCertificate
    eqNodeCount regularNodeCount conceptCount roleCount variableCount

def WireAnchoredCardinalityEqCertificate.decode
    (wire : WireAnchoredCardinalityEqCertificate) :
    Except String DecodedAnchoredCardinalityEqCertificate := do
  if wire.version != 1 then
    throw s!"unsupported anchored cardinality certificate version {wire.version}"
  let decodedAnchored ← wire.anchored.decodeAt wire.concept_count wire.role_count
    wire.variable_count
  let slots ← wire.slots.mapM fun slot => do
    return (← checkedFin "slot source" decodedAnchored.regularNodeCount slot.source,
      ← checkedFin "slot role" wire.role_count slot.role,
      ← checkedFin "slot target" decodedAnchored.regularNodeCount slot.target,
      slot.slot)
  let definitions ← wire.definitions.mapM
    (WireCardinalityDef.decode wire.concept_count wire.role_count)
  return {
    eqNodeCount := decodedAnchored.eqNodeCount
    regularNodeCount := decodedAnchored.regularNodeCount
    conceptCount := wire.concept_count
    roleCount := wire.role_count
    variableCount := wire.variable_count
    positive := decodedAnchored.positive
    certificate := {
      anchored := decodedAnchored.certificate
      slots := slots
      definitions := definitions
    }
  }

def DecodedAnchoredCardinalityEqCertificate.check
    (decoded : DecodedAnchoredCardinalityEqCertificate) : Bool :=
  decoded.certificate.check

theorem DecodedAnchoredCardinalityEqCertificate.check_models
    (decoded : DecodedAnchoredCardinalityEqCertificate)
    (hcheck : decoded.check = true) :
    letI : NeZero decoded.regularNodeCount :=
      ⟨Nat.ne_of_gt decoded.positive⟩
    let interpretation := AnchoredForestDomain.interpretation
      decoded.certificate.anchored.regular.state
      decoded.certificate.anchored.regular.redirect
      decoded.certificate.slotAllowed
      (NominalAnchor decoded.certificate.anchored.nominalRoot)
      decoded.certificate.anchored.regular.rules
      decoded.certificate.anchored.nominalRoot
    interpretation.models decoded.certificate.anchored.equality.base.ontology ∧
      interpretation.modelsCardinalityDefs decoded.certificate.definitions := by
  letI : NeZero decoded.regularNodeCount :=
    ⟨Nat.ne_of_gt decoded.positive⟩
  exact decoded.certificate.check_models hcheck

private def emptyRegularWire : WireRegularCertificate where
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

private def emptyEqState : WireEqState where
  labels := []
  edges := []
  obligations := []
  equalities := []
  representatives := [0]
  representative_paths := [[]]

private def emptyAnchoredWire : WireAnchoredEqCertificate where
  version := 1
  equality_node_count := 1
  regular := emptyRegularWire
  equality_ontology := []
  equality_state := emptyEqState
  class_map := [0]
  nominal_roots := [none]

private def accepted : WireAnchoredCardinalityEqCertificate where
  version := 1
  concept_count := 1
  role_count := 1
  variable_count := 1
  anchored := emptyAnchoredWire
  slots := []
  definitions := []

private def badSlot : WireAnchoredCardinalityEqCertificate :=
  { accepted with slots := [{ source := 1, role := 0, target := 0, slot := 0 }] }

private def badDimensions : WireAnchoredCardinalityEqCertificate :=
  { accepted with concept_count := 2 }

example : (accepted.decode.map (·.check)) = .ok true := by native_decide
example : (match badSlot.decode with
    | .error _ => true | .ok _ => false) = true := by native_decide
example : (match badDimensions.decode with
    | .error _ => true | .ok _ => false) = true := by native_decide

#print axioms DecodedAnchoredCardinalityEqCertificate.check_models

end ContextCalculus.Hypertableau
