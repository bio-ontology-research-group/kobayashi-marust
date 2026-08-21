import ContextCalculus.HypertableauRegularCertificate
import ContextCalculus.HypertableauWire
import Lean

/-!
# Bounded JSON wire for regular hypertableau certificates

All IDs are decoded through `checkedFin`. Redirects must contain exactly one
target per finite node. The decoder rejects zero-node models, malformed role
rules, and out-of-range clause variables before the Boolean semantic checker
runs.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireRolePair where
  premise : Nat
  conclusion : Nat
deriving FromJson, ToJson, Repr

structure WireRoleChain where
  first : Nat
  second : Nat
  conclusion : Nat
deriving FromJson, ToJson, Repr

inductive WireNormalizedRoleClause where
  | subRole (premise conclusion source target : Nat)
  | inverseRole (premise conclusion source target : Nat)
  | chain (first second conclusion source middle target : Nat)
  | reflexive (role source : Nat)
deriving FromJson, ToJson, Repr

def WireNormalizedRoleClause.decode
    (variableCount roleCount : Nat) : WireNormalizedRoleClause → Except String
      (NormalizedRoleClause (Fin variableCount) (Fin roleCount))
  | .subRole premise conclusion source target => do
      return .subRole
        (← checkedFin "role" roleCount premise)
        (← checkedFin "role" roleCount conclusion)
        (← checkedFin "variable" variableCount source)
        (← checkedFin "variable" variableCount target)
  | .inverseRole premise conclusion source target => do
      return .inverseRole
        (← checkedFin "role" roleCount premise)
        (← checkedFin "role" roleCount conclusion)
        (← checkedFin "variable" variableCount source)
        (← checkedFin "variable" variableCount target)
  | .chain first second conclusion source middle target => do
      return .chain
        (← checkedFin "role" roleCount first)
        (← checkedFin "role" roleCount second)
        (← checkedFin "role" roleCount conclusion)
        (← checkedFin "variable" variableCount source)
        (← checkedFin "variable" variableCount middle)
        (← checkedFin "variable" variableCount target)
  | .reflexive role source => do
      return .reflexive
        (← checkedFin "role" roleCount role)
        (← checkedFin "variable" variableCount source)

structure WireRegularCertificate where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  redirect : List Nat
  cover : List WireEdge
  sub_roles : List WireRolePair
  inverse_roles : List WireRolePair
  chains : List WireRoleChain
  reflexive_roles : List Nat
  role_clauses : List WireNormalizedRoleClause
  residual : List WireClause
deriving FromJson, ToJson, Repr

structure DecodedRegularCertificate where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  positive : 0 < nodeCount
  certificate : FiniteRegularCertificate
    nodeCount conceptCount roleCount variableCount

def decodeRedirect (nodeCount : Nat) (values : List Nat) :
    Except String (Fin nodeCount → Fin nodeCount) := do
  let decoded ← values.mapM (checkedFin "redirect node" nodeCount)
  if h : decoded.length = nodeCount then
    return fun node => decoded.get (h.symm ▸ node)
  else
    throw s!"redirect has {decoded.length} entries, expected {nodeCount}"

def WireRegularCertificate.decode (wire : WireRegularCertificate) :
    Except String DecodedRegularCertificate := do
  if wire.version != 1 then
    throw s!"unsupported regular hypertableau certificate version {wire.version}"
  if hpositive : 0 < wire.node_count then
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
    let redirect ← decodeRedirect wire.node_count wire.redirect
    let cover ← wire.cover.mapM fun edge => do
      return (← checkedFin "cover role" wire.role_count edge.role,
        ← checkedFin "cover source" wire.node_count edge.source,
        ← checkedFin "cover target" wire.node_count edge.target)
    let subRoles ← wire.sub_roles.mapM fun rule => do
      return (← checkedFin "subrole premise" wire.role_count rule.premise,
        ← checkedFin "subrole conclusion" wire.role_count rule.conclusion)
    let inverseRoles ← wire.inverse_roles.mapM fun rule => do
      return (← checkedFin "inverse premise" wire.role_count rule.premise,
        ← checkedFin "inverse conclusion" wire.role_count rule.conclusion)
    let chains ← wire.chains.mapM fun rule => do
      return (← checkedFin "chain first role" wire.role_count rule.first,
        ← checkedFin "chain second role" wire.role_count rule.second,
        ← checkedFin "chain conclusion" wire.role_count rule.conclusion)
    let reflexiveRoles ← wire.reflexive_roles.mapM
      (checkedFin "reflexive role" wire.role_count)
    let roleClauses ← wire.role_clauses.mapM
      (WireNormalizedRoleClause.decode wire.variable_count wire.role_count)
    let residual ← wire.residual.mapM
      (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
    return {
      nodeCount := wire.node_count
      conceptCount := wire.concept_count
      roleCount := wire.role_count
      variableCount := wire.variable_count
      positive := hpositive
      certificate := {
        labels := labels
        edges := edges
        obligations := obligations
        redirect := redirect
        cover := cover
        subRoles := subRoles
        inverseRoles := inverseRoles
        chains := chains
        reflexiveRoles := reflexiveRoles
        roleClauses := roleClauses
        residual := residual
      }
    }
  else
    throw "regular hypertableau certificate requires at least one node"

def DecodedRegularCertificate.check
    (decoded : DecodedRegularCertificate) : Bool :=
  decoded.certificate.check

/-- Decoding introduces only finite bounds and positivity evidence. After a
successful decode, the executable regular checker accepts exactly the finite
semantic invariant used by the unravelling proof. -/
theorem DecodedRegularCertificate.check_eq_true_iff_valid
    (decoded : DecodedRegularCertificate) :
    decoded.check = true ↔ decoded.certificate.Valid := by
  exact decoded.certificate.check_eq_true_iff_valid

theorem DecodedRegularCertificate.check_models
    (decoded : DecodedRegularCertificate)
    (hcheck : decoded.check = true) :
    letI : NeZero decoded.nodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
    (decoded.certificate.state.regularUnravelling
      decoded.certificate.redirect (fun _ _ _ _ => True) 0
      decoded.certificate.rules).models decoded.certificate.ontology := by
  letI : NeZero decoded.nodeCount := ⟨Nat.ne_of_gt decoded.positive⟩
  exact decoded.certificate.check_models hcheck

private def validEmptyWire : WireRegularCertificate where
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

example : (validEmptyWire.decode.map (·.check)) = .ok true := by native_decide
example : (match decodeRedirect 1 [] with | .error _ => true | .ok _ => false) =
    true := by native_decide
example : (match checkedFin "node" 1 1 with | .error _ => true | .ok _ => false) =
    true := by native_decide

#print axioms DecodedRegularCertificate.check_models
#print axioms DecodedRegularCertificate.check_eq_true_iff_valid

end ContextCalculus.Hypertableau
