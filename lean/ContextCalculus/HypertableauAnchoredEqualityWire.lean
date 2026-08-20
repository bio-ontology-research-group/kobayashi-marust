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

structure DecodedAnchoredEqAt
    (conceptCount roleCount variableCount : Nat) where
  eqNodeCount : Nat
  regularNodeCount : Nat
  positive : 0 < regularNodeCount
  certificate : FiniteAnchoredEqCertificate
    eqNodeCount regularNodeCount conceptCount roleCount variableCount

def WireAnchoredEqCertificate.decodeAt (wire : WireAnchoredEqCertificate)
    (conceptCount roleCount variableCount : Nat) :
    Except String (DecodedAnchoredEqAt conceptCount roleCount variableCount) := do
  if wire.version != 1 then
    throw s!"unsupported equality-backed anchored certificate version {wire.version}"
  if wire.regular.version != 1 then
    throw s!"unsupported regular hypertableau certificate version {wire.regular.version}"
  if wire.regular.concept_count != conceptCount then
    throw "anchored certificate concept count does not match its container"
  if wire.regular.role_count != roleCount then
    throw "anchored certificate role count does not match its container"
  if wire.regular.variable_count != variableCount then
    throw "anchored certificate variable count does not match its container"
  if hpositive : 0 < wire.regular.node_count then
    let labels ← wire.regular.labels.mapM fun label => do
      return (← checkedFin "node" wire.regular.node_count label.node,
        ← label.literal.decode conceptCount)
    let edges ← wire.regular.edges.mapM fun edge => do
      return (← checkedFin "role" roleCount edge.role,
        ← checkedFin "node" wire.regular.node_count edge.source,
        ← checkedFin "node" wire.regular.node_count edge.target)
    let obligations ← wire.regular.obligations.mapM fun obligation => do
      return (← checkedFin "role" roleCount obligation.role,
        ← obligation.filler.decode conceptCount,
        ← checkedFin "node" wire.regular.node_count obligation.node)
    let redirect ← decodeRedirect wire.regular.node_count wire.regular.redirect
    let cover ← wire.regular.cover.mapM fun edge => do
      return (← checkedFin "cover role" roleCount edge.role,
        ← checkedFin "cover source" wire.regular.node_count edge.source,
        ← checkedFin "cover target" wire.regular.node_count edge.target)
    let subRoles ← wire.regular.sub_roles.mapM fun rule => do
      return (← checkedFin "subrole premise" roleCount rule.premise,
        ← checkedFin "subrole conclusion" roleCount rule.conclusion)
    let inverseRoles ← wire.regular.inverse_roles.mapM fun rule => do
      return (← checkedFin "inverse premise" roleCount rule.premise,
        ← checkedFin "inverse conclusion" roleCount rule.conclusion)
    let chains ← wire.regular.chains.mapM fun rule => do
      return (← checkedFin "chain first role" roleCount rule.first,
        ← checkedFin "chain second role" roleCount rule.second,
        ← checkedFin "chain conclusion" roleCount rule.conclusion)
    let reflexiveRoles ← wire.regular.reflexive_roles.mapM
      (checkedFin "reflexive role" roleCount)
    let roleClauses ← wire.regular.role_clauses.mapM
      (WireNormalizedRoleClause.decode variableCount roleCount)
    let residual ← wire.regular.residual.mapM
      (WireClause.decode variableCount conceptCount roleCount)
    let regular : FiniteRegularCertificate wire.regular.node_count
        conceptCount roleCount variableCount := {
      labels, edges, obligations, redirect, cover, subRoles, inverseRoles,
      chains, reflexiveRoles, roleClauses, residual
    }
    let ontology ← wire.equality_ontology.mapM
      (WireClause.decode variableCount conceptCount roleCount)
    let equality ← wire.equality_state.decode wire.equality_node_count conceptCount
      roleCount variableCount ontology
    let classMap ← decodeClassMap wire.equality_node_count wire.regular.node_count
      wire.class_map
    let nominalRoot ← decodeNominalRoots wire.regular.node_count conceptCount
      wire.nominal_roots
    return {
      eqNodeCount := wire.equality_node_count
      regularNodeCount := wire.regular.node_count
      positive := hpositive
      certificate := { equality, regular, classMap, nominalRoot }
    }
  else throw "regular hypertableau certificate requires at least one node"

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
