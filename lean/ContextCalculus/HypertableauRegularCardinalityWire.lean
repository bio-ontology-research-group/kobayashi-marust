import ContextCalculus.HypertableauRegularCardinalityCertificate
import ContextCalculus.HypertableauRegularWire
import ContextCalculus.HypertableauCardinalityWire
import Lean

/-!
# Bounded wire for regular HT cardinality certificates

The regular graph wire remains the exact ontology payload. This wrapper adds
authorized path slots and first-class cardinality definitions. All identifiers
are checked before constructing dependent finite certificate data.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRegularSlot where
  source : Nat
  role : Nat
  target : Nat
  slot : Nat
deriving FromJson, ToJson, Repr

structure WireRegularCardinalityCertificate where
  version : Nat
  base : WireRegularCertificate
  slots : List WireRegularSlot
  definitions : List WireCardinalityDef
deriving FromJson, ToJson, Repr

structure DecodedRegularCardinalityCertificate where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  positive : 0 < nodeCount
  certificate : FiniteRegularCardinalityCertificate
    nodeCount conceptCount roleCount variableCount

def WireRegularCardinalityCertificate.decode
    (wire : WireRegularCardinalityCertificate) :
    Except String DecodedRegularCardinalityCertificate := do
  if wire.version != 1 then
    throw s!"unsupported regular cardinality certificate version {wire.version}"
  let decodedBase ← wire.base.decode
  let slots ← wire.slots.mapM fun slot => do
    return (← checkedFin "slot source" decodedBase.nodeCount slot.source,
      ← checkedFin "slot role" decodedBase.roleCount slot.role,
      ← checkedFin "slot target" decodedBase.nodeCount slot.target,
      slot.slot)
  let definitions ← wire.definitions.mapM
    (WireCardinalityDef.decode decodedBase.conceptCount decodedBase.roleCount)
  return {
    nodeCount := decodedBase.nodeCount
    conceptCount := decodedBase.conceptCount
    roleCount := decodedBase.roleCount
    variableCount := decodedBase.variableCount
    positive := decodedBase.positive
    certificate := {
      base := decodedBase.certificate
      slots := slots
      definitions := definitions
    }
  }

def DecodedRegularCardinalityCertificate.check
    (decoded : DecodedRegularCardinalityCertificate) : Bool :=
  decoded.certificate.check

theorem DecodedRegularCardinalityCertificate.check_models
    (decoded : DecodedRegularCardinalityCertificate)
    (hcheck : decoded.check = true) :
    letI : NeZero decoded.nodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
    let interpretation := decoded.certificate.base.state.regularUnravelling
      decoded.certificate.base.redirect decoded.certificate.slotAllowed 0
      decoded.certificate.base.rules
    interpretation.models decoded.certificate.base.ontology ∧
      interpretation.modelsCardinalityDefs decoded.certificate.definitions := by
  letI : NeZero decoded.nodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
  exact decoded.certificate.check_models hcheck

private def emptyBaseWire : WireRegularCertificate where
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

private def emptyCardinalityWire : WireRegularCardinalityCertificate where
  version := 1
  base := emptyBaseWire
  slots := []
  definitions := []

private def outOfRangeSlotWire : WireRegularCardinalityCertificate where
  version := 1
  base := emptyBaseWire
  slots := [{ source := 1, role := 0, target := 0, slot := 0 }]
  definitions := []

example : (emptyCardinalityWire.decode.map (·.check)) = .ok true := by native_decide
example : (match outOfRangeSlotWire.decode with
    | .error _ => true | .ok _ => false) = true := by native_decide

#print axioms DecodedRegularCardinalityCertificate.check_models

end ContextCalculus.Hypertableau
