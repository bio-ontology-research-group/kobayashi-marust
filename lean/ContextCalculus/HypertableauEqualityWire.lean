import ContextCalculus.HypertableauEqualityCertificate
import ContextCalculus.HypertableauWire
import Lean

/-!
# Version-2 equality-aware hypertableau certificate wire format

Version 1 remains unchanged and equality-free. Version 2 carries an exact
finite equality state at the root and at every head-branch successor. All
natural-number identifiers are bounds checked before the proved equality-aware
checker sees them.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireEquality where
  left : Nat
  right : Nat
deriving FromJson, ToJson, Repr

structure WireEqState where
  labels : List WireLabel
  edges : List WireEdge
  obligations : List WireObligation
  equalities : List WireEquality
  representatives : List Nat
  representative_paths : List (List Nat)
deriving FromJson, ToJson, Repr

inductive WireEqRefutationTree where
  | clash
  | branch (clause : Nat) (assignment : List Nat)
      (children : List (WireEqState × WireEqRefutationTree))
  | witness (source target role : Nat) (filler : WireLit)
      (child : WireEqRefutationTree)
deriving FromJson, ToJson, Repr

inductive WireEqEvidence where
  | unsat (tree : WireEqRefutationTree)
deriving FromJson, ToJson, Repr

structure WireEqCertificate where
  version : Nat
  node_count : Nat
  concept_count : Nat
  role_count : Nat
  variable_count : Nat
  ontology : List WireClause
  state : WireEqState
  evidence : WireEqEvidence
deriving FromJson, ToJson, Repr

def decodeNodeVector (kind : String) (nodeCount : Nat) (values : List Nat) :
    Except String (Fin nodeCount → Fin nodeCount) := do
  let decoded ← values.mapM (checkedFin kind nodeCount)
  if h : decoded.length = nodeCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"{kind} has {decoded.length} entries, expected {nodeCount}"

def decodeNodePaths (nodeCount : Nat) (paths : List (List Nat)) :
    Except String (Fin nodeCount → List (Fin nodeCount)) := do
  let decoded ← paths.mapM fun path => path.mapM (checkedFin "path node" nodeCount)
  if h : decoded.length = nodeCount then
    return fun index => decoded.get (h.symm ▸ index)
  else
    throw s!"representative_paths has {decoded.length} entries, expected {nodeCount}"

def WireEqState.decode
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (wire : WireEqState) : Except String
      (FiniteEqCertificate nodeCount conceptCount roleCount variableCount) := do
  let labels ← wire.labels.mapM fun label => do
    return (← checkedFin "node" nodeCount label.node,
      ← label.literal.decode conceptCount)
  let edges ← wire.edges.mapM fun edge => do
    return (← checkedFin "role" roleCount edge.role,
      ← checkedFin "node" nodeCount edge.source,
      ← checkedFin "node" nodeCount edge.target)
  let obligations ← wire.obligations.mapM fun obligation => do
    return (← checkedFin "role" roleCount obligation.role,
      ← obligation.filler.decode conceptCount,
      ← checkedFin "node" nodeCount obligation.node)
  let equalities ← wire.equalities.mapM fun equality => do
    return (← checkedFin "equality node" nodeCount equality.left,
      ← checkedFin "equality node" nodeCount equality.right)
  let representative ← decodeNodeVector "representatives" nodeCount wire.representatives
  let representativePath ← decodeNodePaths nodeCount wire.representative_paths
  return {
    base := { ontology, labels, edges, obligations }
    equalities, representative, representativePath
  }

def buildEqChildren :
    List (Atom (Fin variableCount) (Fin conceptCount) (Fin roleCount)) →
    List (FiniteEqCertificate nodeCount conceptCount roleCount variableCount ×
      FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount) →
    Except String (FiniteEqRefutationChildren nodeCount conceptCount roleCount variableCount)
  | [], [] => return .nil
  | head :: heads, (state, tree) :: children =>
      return .cons head state tree (← buildEqChildren heads children)
  | _, _ => throw "decoded equality-refutation child count mismatch"

partial def WireEqRefutationTree.decode
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :
    WireEqRefutationTree → Except String
      (FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount)
  | .clash => return .clash
  | .branch clauseIndex assignment children => do
      let clause ← match ontology[clauseIndex]? with
        | some clause => pure clause
        | none => throw s!"clause id {clauseIndex} is outside the ontology"
      let decodedAssignment ← decodeAssignment nodeCount variableCount assignment
      if children.length = clause.head.length then
        let decodedChildren ← children.mapM fun child => do
          let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
          let tree ← child.2.decode nodeCount conceptCount roleCount variableCount ontology
          return (state, tree)
        return .branch clause decodedAssignment
          (← buildEqChildren clause.head decodedChildren)
      else
        throw s!"branch has {children.length} children, expected {clause.head.length}"
  | .witness source target role filler child => do
      return .witness
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
        (← checkedFin "role" roleCount role)
        (← filler.decode conceptCount)
        (← child.decode nodeCount conceptCount roleCount variableCount ontology)

structure DecodedEqCertificate where
  nodeCount : Nat
  conceptCount : Nat
  roleCount : Nat
  variableCount : Nat
  certificate : FiniteEqCertificate nodeCount conceptCount roleCount variableCount
  tree : FiniteEqRefutationTree nodeCount conceptCount roleCount variableCount

def WireEqCertificate.decode (wire : WireEqCertificate) : Except String DecodedEqCertificate := do
  if wire.version != 2 then
    throw s!"unsupported equality hypertableau certificate version {wire.version}"
  let ontology ← wire.ontology.mapM
    (WireClause.decode wire.variable_count wire.concept_count wire.role_count)
  let certificate ← wire.state.decode wire.node_count wire.concept_count
    wire.role_count wire.variable_count ontology
  let tree ← match wire.evidence with
    | .unsat tree =>
        WireEqRefutationTree.decode wire.node_count wire.concept_count wire.role_count wire.variable_count ontology tree
  return {
    nodeCount := wire.node_count
    conceptCount := wire.concept_count
    roleCount := wire.role_count
    variableCount := wire.variable_count
    certificate, tree
  }

def DecodedEqCertificate.check (decoded : DecodedEqCertificate) : Bool :=
  decide (0 < decoded.nodeCount) &&
  decoded.certificate.base.labels.isEmpty &&
  decoded.certificate.base.edges.isEmpty &&
  decoded.certificate.base.obligations.isEmpty &&
  decoded.tree.check decoded.certificate

def WireEqCertificate.check (wire : WireEqCertificate) : Except String Bool := do
  return (← wire.decode).check

theorem DecodedEqCertificate.check_sound (decoded : DecodedEqCertificate)
    (hcheck : decoded.check = true) :
    ¬∃ (Domain : Type) (I : Interp Domain (Fin decoded.conceptCount)
        (Fin decoded.roleCount)),
      Nonempty Domain ∧ I.models decoded.certificate.base.ontology := by
  simp only [DecodedEqCertificate.check, Bool.and_eq_true, decide_eq_true_eq,
    List.isEmpty_iff] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hpositive, hlabels⟩, hedges⟩, hobligations⟩, htree⟩
  haveI : Nonempty (Fin decoded.nodeCount) := ⟨⟨0, hpositive⟩⟩
  exact decoded.tree.check_ontology_unsatisfiable decoded.certificate
    ⟨hlabels, hedges, hobligations⟩ htree

namespace EqualityWireTests

private def equalityClause : WireClause :=
  { body := [], head := [.eq 0 2] }

private def rootState : WireEqState where
  labels := []
  edges := []
  obligations := []
  equalities := []
  representatives := [0, 1, 2]
  representative_paths := [[], [], []]

private def childState : WireEqState where
  labels := []
  edges := []
  obligations := []
  equalities := [{ left := 0, right := 2 }]
  representatives := [0, 1, 0]
  representative_paths := [[], [], [0]]

private def contradiction : WireClause :=
  { body := [.eq 0 2], head := [] }

private def accepted : WireEqCertificate where
  version := 2
  node_count := 3
  concept_count := 1
  role_count := 1
  variable_count := 3
  ontology := [equalityClause, contradiction]
  state := rootState
  evidence := .unsat (.branch 0 [0, 1, 2]
    [(childState, .branch 1 [0, 1, 2] [])])

example : accepted.check = .ok true := by native_decide

private def stale : WireEqCertificate :=
  { accepted with evidence := .unsat (.branch 0 [0, 1, 2]
      [(rootState, .branch 1 [0, 1, 2] [])]) }

example : stale.check = .ok false := by native_decide

private def badPath : WireEqCertificate :=
  { accepted with evidence := .unsat (.branch 0 [0, 1, 2]
      [({ childState with representative_paths := [[], [], []] },
        .branch 1 [0, 1, 2] [])]) }

example : badPath.check = .ok false := by native_decide

private def outOfBounds : WireEqCertificate :=
  { accepted with state := { rootState with representatives := [0, 1, 3] } }

example : outOfBounds.check = .error "representatives id 3 is outside [0,3)" := by
  native_decide

end EqualityWireTests

#print axioms DecodedEqCertificate.check_sound

end ContextCalculus.Hypertableau
