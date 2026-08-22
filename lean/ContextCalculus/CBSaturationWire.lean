import ContextCalculus.CBSaturationCertificate
import Lean

/-!
# JSON wire boundary for finite CB saturation certificates

Every numeric atom is bounds-checked before it can enter the semantic checker.
Clause sides must be duplicate-free, the wire version is fixed, and all trace
references are checked by `CBSaturationCertificate`.
-/

namespace ContextCalculus.CBCert

open Lean

structure WireClause where
  neg : List Nat
  pos : List Nat
deriving FromJson, ToJson

inductive WireJustification where
  | premise (index : Nat)
  | resolve (positive negative atom : Nat)
deriving FromJson, ToJson

structure WireEntry where
  clause : WireClause
  justification : WireJustification
deriving FromJson, ToJson

structure WireCertificate where
  version : Nat
  atom_count : Nat
  premises : List WireClause
  trace : List WireEntry
deriving FromJson, ToJson

def checkedFin (n value : Nat) : Except String (Fin n) :=
  if h : value < n then .ok ⟨value, h⟩
  else .error s!"atom id {value} is outside [0,{n})"

def decodeAtomSide (n : Nat) (side : List Nat) : Except String (Finset (Fin n)) := do
  if side.Nodup then
    return (← side.mapM (checkedFin n)).toFinset
  else do
    throw "clause side contains a duplicate atom"

def WireClause.decode (n : Nat) (clause : WireClause) : Except String (Clause n) := do
  return ⟨← decodeAtomSide n clause.neg, ← decodeAtomSide n clause.pos⟩

def WireJustification.decode (n : Nat) :
    WireJustification → Except String (Justification n)
  | .premise index => return .premise index
  | .resolve positive negative atom =>
      return .resolve positive negative (← checkedFin n atom)

def WireEntry.decode (n : Nat) (entry : WireEntry) : Except String (Entry n) := do
  return ⟨← entry.clause.decode n, ← entry.justification.decode n⟩

structure DecodedCertificate where
  atomCount : Nat
  certificate : Certificate atomCount

def WireCertificate.decode (document : WireCertificate) : Except String DecodedCertificate := do
  if document.version != 1 then
    throw s!"unsupported CB saturation certificate version {document.version}"
  else if document.atom_count = 0 then
    throw "atom_count must be positive"
  else do
    let premises ← document.premises.mapM (WireClause.decode document.atom_count)
    let trace ← document.trace.mapM (WireEntry.decode document.atom_count)
    return DecodedCertificate.mk document.atom_count
      { premises := premises, trace := trace }

def WireCertificate.check (document : WireCertificate) : Except String Bool := do
  return (← document.decode).certificate.check

theorem DecodedCertificate.check_saturation (document : DecodedCertificate)
    (hcheck : document.certificate.check = true) :
    Equiv.Saturation document.certificate.premises.toFinset
      document.certificate.terminal :=
  document.certificate.check_saturation hcheck

theorem DecodedCertificate.check_models_iff (document : DecodedCertificate)
    (hcheck : document.certificate.check = true)
    (interpretation : Atom document.atomCount → Prop) :
    Equiv.Models document.certificate.terminal interpretation ↔
      Equiv.Models document.certificate.premises.toFinset interpretation :=
  document.certificate.check_models_iff hcheck interpretation

private def acceptedWireExample : WireCertificate where
  version := 1
  atom_count := 2
  premises := [⟨[], [0]⟩, ⟨[0], [1]⟩]
  trace :=
    [ ⟨⟨[], [0]⟩, .premise 0⟩
    , ⟨⟨[0], [1]⟩, .premise 1⟩
    , ⟨⟨[], [1]⟩, .resolve 0 1 0⟩ ]

example : acceptedWireExample.check = .ok true := by native_decide

private def exceptIsError {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

private def outOfBoundsWireExample : WireCertificate :=
  { acceptedWireExample with premises := [⟨[], [2]⟩] }

example : exceptIsError outOfBoundsWireExample.check = true := by native_decide

private def duplicateWireExample : WireCertificate :=
  { acceptedWireExample with premises := [⟨[], [0, 0]⟩] }

example : exceptIsError duplicateWireExample.check = true := by native_decide

#print axioms DecodedCertificate.check_saturation
#print axioms DecodedCertificate.check_models_iff

end ContextCalculus.CBCert
