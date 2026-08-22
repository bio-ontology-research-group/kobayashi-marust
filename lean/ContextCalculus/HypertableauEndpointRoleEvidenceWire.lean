import ContextCalculus.HypertableauEndpointRoleEvidence
import ContextCalculus.HypertableauRegularWire

/-! # JSON wire for endpoint-role derivations -/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireEndpointRoleEvidence where
  | direct (role source target : Nat)
  | sub (premise conclusion source target : Nat)
      (child : WireEndpointRoleEvidence)
  | inverse (premise conclusion source target : Nat)
      (child : WireEndpointRoleEvidence)
  | chain (first second conclusion source middle target : Nat)
      (left right : WireEndpointRoleEvidence)
  | refl (role source : Nat)
deriving FromJson, ToJson, Repr

def WireEndpointRoleEvidence.decode (nodeCount roleCount : Nat) :
    WireEndpointRoleEvidence → Except String
      (FiniteEndpointRoleEvidence (Fin nodeCount) (Fin roleCount))
  | .direct role source target => do
      return .direct (← checkedFin "role" roleCount role)
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
  | .sub premise conclusion source target child => do
      return .sub (← checkedFin "role" roleCount premise)
        (← checkedFin "role" roleCount conclusion)
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
        (← child.decode nodeCount roleCount)
  | .inverse premise conclusion source target child => do
      return .inverse (← checkedFin "role" roleCount premise)
        (← checkedFin "role" roleCount conclusion)
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
        (← child.decode nodeCount roleCount)
  | .chain first second conclusion source middle target left right => do
      return .chain (← checkedFin "role" roleCount first)
        (← checkedFin "role" roleCount second)
        (← checkedFin "role" roleCount conclusion)
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount middle)
        (← checkedFin "node" nodeCount target)
        (← left.decode nodeCount roleCount)
        (← right.decode nodeCount roleCount)
  | .refl role source => do
      return .refl (← checkedFin "role" roleCount role)
        (← checkedFin "node" nodeCount source)

structure WireEndpointRoleEvidenceDocument where
  version : Nat
  certificate : WireRegularCertificate
  evidence : WireEndpointRoleEvidence
deriving FromJson, ToJson, Repr

structure DecodedEndpointRoleEvidenceDocument where
  decoded : DecodedRegularCertificate
  evidence : FiniteEndpointRoleEvidence
    (Fin decoded.nodeCount) (Fin decoded.roleCount)

def WireEndpointRoleEvidenceDocument.decode
    (wire : WireEndpointRoleEvidenceDocument) :
    Except String DecodedEndpointRoleEvidenceDocument := do
  if wire.version != 1 then
    throw s!"unsupported endpoint-role evidence version {wire.version}"
  let decoded ← wire.certificate.decode
  let evidence ← wire.evidence.decode decoded.nodeCount decoded.roleCount
  return { decoded, evidence }

def DecodedEndpointRoleEvidenceDocument.check
    (document : DecodedEndpointRoleEvidenceDocument) : Bool :=
  document.evidence.check document.decoded.certificate

theorem DecodedEndpointRoleEvidenceDocument.check_sound
    (document : DecodedEndpointRoleEvidenceDocument)
    (hcheck : document.check = true) :
    EndpointRole document.decoded.certificate.state
      document.decoded.certificate.redirect document.decoded.certificate.rules
      document.evidence.role document.evidence.source
      document.evidence.target :=
  document.evidence.check_sound document.decoded.certificate hcheck

#print axioms DecodedEndpointRoleEvidenceDocument.check_sound

end ContextCalculus.Hypertableau
