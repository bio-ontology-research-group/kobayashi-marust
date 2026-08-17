import ContextCalculus.HypertableauRefutationCertificate
import Lean

/-!
# JSON wire format for hypertableau certificates

All ids and assignments arrive as untrusted natural numbers.  Decoding checks
every bound before constructing finite semantic objects.  The decoded SAT and
UNSAT payloads are then accepted only by the proved executable checkers.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireLit where
  concept : Nat
  neg : Bool
deriving FromJson, ToJson, Repr

inductive WireAtom where
  | concept (literal : WireLit) (node : Nat)
  | role (role source target : Nat)
  | exists_ (role : Nat) (filler : WireLit) (node : Nat)
  | eq (left right : Nat)
deriving FromJson, ToJson, Repr

structure WireClause where
  body : List WireAtom
  head : List WireAtom
deriving FromJson, ToJson, Repr

structure WireLabel where
  node : Nat
  literal : WireLit
deriving FromJson, ToJson, Repr

structure WireEdge where
  role : Nat
  source : Nat
  target : Nat
deriving FromJson, ToJson, Repr

structure WireObligation where
  role : Nat
  filler : WireLit
  node : Nat
deriving FromJson, ToJson, Repr

inductive WireRefutationTree where
  | clash
  | branch (clause : Nat) (assignment : List Nat)
      (children : List WireRefutationTree)
deriving FromJson, ToJson, Repr

inductive WireEvidence where
  | sat
  | unsat (tree : WireRefutationTree)
deriving FromJson, ToJson, Repr

structure WireCertificate where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  evidence : WireEvidence
deriving FromJson, ToJson, Repr

def checkedFin (kind : String) (bound value : Nat) : Except String (Fin bound) :=
  if h : value < bound then .ok ⟨value, h⟩
  else .error s!"{kind} id {value} is outside [0,{bound})"

def WireLit.decode (conceptCount : Nat) (literal : WireLit) :
    Except String (Lit (Fin conceptCount)) := do
  return ⟨← checkedFin "concept" conceptCount literal.concept, literal.neg⟩

def WireAtom.decode (variableCount conceptCount roleCount : Nat) : WireAtom →
    Except String (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  | .concept literal node => do
      return .concept (← literal.decode conceptCount)
        (← checkedFin "variable" variableCount node)
  | .role relation source target => do
      return .role (← checkedFin "role" roleCount relation)
        (← checkedFin "variable" variableCount source)
        (← checkedFin "variable" variableCount target)
  | .exists_ relation filler node => do
      return .exists_ (← checkedFin "role" roleCount relation)
        (← filler.decode conceptCount) (← checkedFin "variable" variableCount node)
  | .eq left right => do
      return .eq (← checkedFin "variable" variableCount left)
        (← checkedFin "variable" variableCount right)

def WireClause.decode (variableCount conceptCount roleCount : Nat)
    (clause : WireClause) : Except String
      (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)) := do
  return ⟨← clause.body.mapM (WireAtom.decode variableCount conceptCount roleCount),
    ← clause.head.mapM (WireAtom.decode variableCount conceptCount roleCount)⟩

def decodeAssignment (nodeCount variableCount : Nat) (values : List Nat) :
    Except String (Fin variableCount → Fin nodeCount) := do
  let decoded ← values.mapM (checkedFin "node" nodeCount)
  if h : decoded.length = variableCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"assignment has {decoded.length} entries, expected {variableCount}"

structure DecodedCertificate where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount

def WireCertificate.decodeBase (wire : WireCertificate) : Except String DecodedCertificate := do
  if wire.version != 1 then
    throw s!"unsupported hypertableau certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
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
    variableCount := wire.variable_count
    certificate := { ontology, labels, edges, obligations }
  }

def buildChildren :
    List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) →
    List (FiniteRefutationTree nodeCount conceptCount roleCount variableCount) →
    Except String
      (FiniteRefutationChildren nodeCount conceptCount roleCount variableCount)
  | [], [] => return .nil
  | head :: heads, tree :: trees =>
      return .cons head tree (← buildChildren heads trees)
  | _, _ => throw "decoded refutation child count mismatch"

partial def WireRefutationTree.decode
    (certificate : FiniteSatCertificate nodeCount conceptCount roleCount variableCount) :
    WireRefutationTree → Except String
      (FiniteRefutationTree nodeCount conceptCount roleCount variableCount)
  | .clash => return .clash
  | .branch clauseIndex assignment children => do
      let clause ← match certificate.ontology[clauseIndex]? with
        | some clause => pure clause
        | none => throw s!"clause id {clauseIndex} is outside the ontology"
      let decodedAssignment ← decodeAssignment nodeCount variableCount assignment
      if children.length = clause.head.length then
        let decodedChildren ← children.mapM (WireRefutationTree.decode certificate)
        return .branch clause decodedAssignment
          (← buildChildren clause.head decodedChildren)
      else
        throw s!"branch has {children.length} children, expected {clause.head.length}"

inductive DecodedEvidence where
  | sat (decoded : DecodedCertificate)
  | unsat (decoded : DecodedCertificate)
      (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
        decoded.roleCount decoded.variableCount)

def WireCertificate.decode (wire : WireCertificate) : Except String DecodedEvidence := do
  let decoded ← wire.decodeBase
  match wire.evidence with
  | .sat => return .sat decoded
  | .unsat tree => return .unsat decoded (← tree.decode decoded.certificate)

def DecodedEvidence.check : DecodedEvidence → Bool
  | .sat decoded => decoded.certificate.checkSat
  | .unsat decoded tree =>
      decide (0 < decoded.nodeCount) &&
      decoded.certificate.labels.isEmpty &&
      decoded.certificate.edges.isEmpty &&
      decoded.certificate.obligations.isEmpty &&
      tree.check decoded.certificate

def WireCertificate.check (wire : WireCertificate) : Except String Bool := do
  return (← wire.decode).check

theorem DecodedEvidence.sat_sound (decoded : DecodedCertificate)
    (hcheck : (DecodedEvidence.sat decoded).check = true) :
    ∃ I : Interp (Fin decoded.nodeCount) (Fin decoded.conceptCount)
        (Fin decoded.roleCount),
      I.models decoded.certificate.ontology :=
  decoded.certificate.checkSat_satisfiable hcheck

theorem DecodedEvidence.unsat_sound (decoded : DecodedCertificate)
    (tree : FiniteRefutationTree decoded.nodeCount decoded.conceptCount
      decoded.roleCount decoded.variableCount)
    (hcheck : (DecodedEvidence.unsat decoded tree).check = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
        (Fin decoded.roleCount)), Nonempty Domain ∧
      I.models decoded.certificate.ontology := by
  simp only [DecodedEvidence.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hnode, hlabels⟩, hedges⟩, hobligations⟩,
    hrefutation⟩
  letI : Nonempty (Fin decoded.nodeCount) :=
    ⟨⟨0, hnode⟩⟩
  have hempty : decoded.certificate.EmptyRoot := by
    simp only [List.isEmpty_iff] at hlabels hedges hobligations
    exact ⟨hlabels, hedges, hobligations⟩
  exact tree.check_ontology_unsatisfiable decoded.certificate hempty hrefutation

namespace WireTests

private def failed : Except String Bool → Bool
  | .error _ => true
  | .ok _ => false

private def satDocument : WireCertificate where
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

example : satDocument.check = .ok true := by native_decide

private def contradiction : WireClause := { body := [], head := [] }

private def unsatDocument : WireCertificate where
  version := 1
  node_count := 1
  concept_count := 1
  role_count := 1
  variable_count := 0
  ontology := [contradiction]
  labels := []
  edges := []
  obligations := []
  evidence := .unsat (.branch 0 [] [])

example : unsatDocument.check = .ok true := by native_decide

private def badConceptDocument : WireCertificate :=
  { satDocument with
    variable_count := 1
    ontology := [{ body := [], head := [.concept ⟨1, false⟩ 0] }] }

example : failed badConceptDocument.check = true := by native_decide

private def missingBranchDocument : WireCertificate :=
  { unsatDocument with
    variable_count := 1
    ontology := [{ body := [], head := [.concept ⟨0, false⟩ 0] }]
    evidence := .unsat (.branch 0 [0] []) }

example : failed missingBranchDocument.check = true := by native_decide

private def equalityDocument : WireCertificate :=
  { unsatDocument with
    variable_count := 1
    ontology := [{ body := [], head := [.eq 0 0] }]
    evidence := .unsat (.branch 0 [0] [.clash]) }

example : equalityDocument.check = .ok false := by native_decide

private def badVersionDocument : WireCertificate := { satDocument with version := 2 }

example : failed badVersionDocument.check = true := by native_decide

end WireTests

#print axioms DecodedEvidence.sat_sound
#print axioms DecodedEvidence.unsat_sound

end ContextCalculus.Hypertableau
