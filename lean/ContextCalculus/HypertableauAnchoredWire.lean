import ContextCalculus.HypertableauAnchoredCertificate
import ContextCalculus.HypertableauRegularWire
import Lean

/-!
# Bounded wire for anchored HT finite premises

The nominal-root vector has one optional node per concept. All identifiers and
vector lengths are checked before the executable semantic premise checker runs.
-/

namespace ContextCalculus.Hypertableau

open Lean
open AnchoredForestDomain

structure WireAnchoredPremises where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  redirect : List Nat
  nominal_roots : List (Option Nat)
deriving FromJson, ToJson, Repr

structure DecodedAnchoredPremises where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  certificate : FiniteSatCertificate nodeCount conceptCount roleCount 0
  redirect : Fin nodeCount → Fin nodeCount
  nominalRoot : Fin conceptCount → Option (Fin nodeCount)

def decodeNominalRoots (nodeCount conceptCount : Nat)
    (values : List (Option Nat)) :
    Except String (Fin conceptCount → Option (Fin nodeCount)) := do
  let decoded ← values.mapM fun value =>
    match value with
    | none => pure none
    | some node => do
        let decoded ← checkedFin "nominal root" nodeCount node
        pure (some decoded)
  if h : decoded.length = conceptCount then
    return fun concept => decoded.get (h.symm ▸ concept)
  else
    throw s!"nominal_roots has {decoded.length} entries, expected {conceptCount}"

def WireAnchoredPremises.decode (wire : WireAnchoredPremises) :
    Except String DecodedAnchoredPremises := do
  if wire.version != 1 then
    throw s!"unsupported anchored HT premise version {wire.version}"
  let labels ← wire.labels.mapM fun label => do
    return (← checkedFin "node" wire.node_count label.node,
      ← label.literal.decode wire.concept_count)
  let edges ← wire.edges.mapM fun edge => do
    return (← checkedFin "role" wire.role_count edge.role,
      ← checkedFin "node" wire.node_count edge.source,
      ← checkedFin "node" wire.node_count edge.target)
  let obligations ← wire.obligations.mapM fun obligation => do
    return (← checkedFin "role" wire.role_count obligation.role,
      ← obligation.filler.decode wire.concept_count,
      ← checkedFin "node" wire.node_count obligation.node)
  return {
    nodeCount := wire.node_count
    conceptCount := wire.concept_count
    roleCount := wire.role_count
    certificate := { ontology := [], labels, edges, obligations }
    redirect := ← decodeRedirect wire.node_count wire.redirect
    nominalRoot := ← decodeNominalRoots wire.node_count wire.concept_count
      wire.nominal_roots
  }

def DecodedAnchoredPremises.check (decoded : DecodedAnchoredPremises) : Bool :=
  finitePremisesB decoded.certificate decoded.redirect decoded.nominalRoot

def WireAnchoredPremises.check (wire : WireAnchoredPremises) : Except String Bool := do
  return (← wire.decode).check

def DecodedAnchoredPremises.SemanticallyCorrect
    (decoded : DecodedAnchoredPremises) : Prop :=
  decoded.certificate.state.ClashFree ∧
    NominalLabelCoherent decoded.certificate.state
      (NominalAnchor decoded.nominalRoot) decoded.nominalRoot ∧
    RedirectWitnessComplete decoded.certificate.state decoded.redirect

theorem DecodedAnchoredPremises.check_sound
    (decoded : DecodedAnchoredPremises) (hcheck : decoded.check = true) :
    decoded.SemanticallyCorrect :=
  finitePremisesB_sound decoded.certificate decoded.redirect
    decoded.nominalRoot hcheck

private def validWire : WireAnchoredPremises where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
  labels := [{ node := 0, literal := { concept := 0, neg := false } }]
  edges := []
  obligations := []
  redirect := [0]
  nominal_roots := [some 0]

example : validWire.check = .ok true := by native_decide

private def forgedRoot : WireAnchoredPremises :=
  { validWire with node_count := 2, redirect := [0, 1], nominal_roots := [some 1] }

example : forgedRoot.check = .ok false := by native_decide

private def wrongRootLength : WireAnchoredPremises :=
  { validWire with nominal_roots := [] }

example : (match wrongRootLength.check with | .error _ => true | .ok _ => false) = true := by
  native_decide

#print axioms DecodedAnchoredPremises.check_sound

end ContextCalculus.Hypertableau
