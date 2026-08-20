import ContextCalculus.HypertableauCardinalityRuntimeSearch
import ContextCalculus.HypertableauCardinalityRefutationWire
import Lean

/-!
# Wire format for distinct-aware cardinality refutations

Every apart endpoint and tree identifier is bounds checked.  Maximum children
use an exact square matrix; minimum has one exact successor state and child.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireApart where
  left : Nat
  right : Nat
deriving FromJson, ToJson, Repr

structure WireDistinctEqState where
  base : WireEqState
  apart : List WireApart
deriving FromJson, ToJson, Repr

def WireDistinctEqState.decode
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (wire : WireDistinctEqState) : Except String
      (FiniteDistinctEqCertificate nodeCount conceptCount roleCount variableCount) := do
  let base ← wire.base.decode nodeCount conceptCount roleCount variableCount ontology
  let apart ← wire.apart.mapM fun pair => do
    return (← checkedFin "apart node" nodeCount pair.left,
      ← checkedFin "apart node" nodeCount pair.right)
  return ⟨base, apart⟩

inductive WireDistinctCardinalityRefutationTree where
  | equality (tree : WireEqRefutationTree)
  | clash
  | equality_apart (left right : Nat)
  | delay (child : WireDistinctCardinalityRefutationTree)
  | branch (clause : Nat) (assignment : List Nat)
      (children : List (WireDistinctEqState × WireDistinctCardinalityRefutationTree))
  | witness (source target role : Nat) (filler : WireLit)
      (child : WireDistinctCardinalityRefutationTree)
  | maximum (definition source : Nat) (witnesses : List Nat)
      (children : List (List (WireDistinctEqState ×
        WireDistinctCardinalityRefutationTree)))
  | minimum (definition source : Nat) (targets : List Nat)
      (next : WireDistinctEqState) (child : WireDistinctCardinalityRefutationTree)
deriving FromJson, ToJson, Repr

def WireDistinctCardinalityRefutationTree.decodeAtDepth
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    (depth : Nat) → WireDistinctCardinalityRefutationTree → Except String
      (FiniteDistinctCardinalityRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
  | 0, .equality tree => do
      return .equality (← tree.decode nodeCount conceptCount roleCount variableCount ontology)
  | 0, .clash => return .clash
  | 0, .equality_apart left right => do
      return .equalityApart
        (← checkedFin "apart node" nodeCount left)
        (← checkedFin "apart node" nodeCount right)
  | depth + 1, .delay child => do
      return .delay (← child.decodeAtDepth nodeCount conceptCount roleCount variableCount
        ontology definitions depth)
  | depth + 1, .maximum definitionIndex source witnesses children => do
      let definition ← match definitions[definitionIndex]? with
        | some definition => pure definition
        | none => throw s!"cardinality definition id {definitionIndex} is outside the definition list"
      let width := definition.bound + 1
      let decodedWitnesses ← witnesses.mapM (checkedFin "cardinality witness" nodeCount)
      let witnessVector ← decodeExactVector "cardinality witnesses" width decodedWitnesses
      let decodedRows ← children.mapM fun row => do
        let decodedRow ← row.mapM fun child => do
          let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
          let tree ← child.2.decodeAtDepth nodeCount conceptCount roleCount variableCount
            ontology definitions depth
          return (state, tree)
        decodeExactVector "distinct maximum child row" width decodedRow
      let childMatrix ← decodeExactVector "distinct maximum child rows" width decodedRows
      return .maximum definition
        (← checkedFin "node" nodeCount source)
        witnessVector
        (fun left right => (childMatrix left right).1)
        (fun left right => (childMatrix left right).2)
  | depth + 1, .branch clauseIndex assignment children => do
      let clause ← match ontology[clauseIndex]? with
        | some clause => pure clause
        | none => throw s!"clause id {clauseIndex} is outside the ontology"
      let decodedAssignment ← decodeAssignment nodeCount variableCount assignment
      let decodedChildren ← children.mapM fun child => do
        let state ← child.1.decode nodeCount conceptCount roleCount variableCount ontology
        let tree ← child.2.decodeAtDepth nodeCount conceptCount roleCount variableCount
          ontology definitions depth
        return (state, tree)
      let childVector ← decodeExactVector "distinct branch children"
        clause.head.length decodedChildren
      return .branch clause decodedAssignment
        (fun index => (childVector index).1)
        (fun index => (childVector index).2)
  | depth + 1, .witness source target role filler child => do
      return .witness
        (← checkedFin "node" nodeCount source)
        (← checkedFin "node" nodeCount target)
        (← checkedFin "role" roleCount role)
        (← filler.decode conceptCount)
        (← child.decodeAtDepth nodeCount conceptCount roleCount variableCount
          ontology definitions depth)
  | depth + 1, .minimum definitionIndex source targets next child => do
      let definition ← match definitions[definitionIndex]? with
        | some definition => pure definition
        | none => throw s!"cardinality definition id {definitionIndex} is outside the definition list"
      let decodedTargets ← targets.mapM (checkedFin "minimum target" nodeCount)
      let targetVector ← decodeExactVector "minimum targets" definition.bound decodedTargets
      return .minimum definition
        (← checkedFin "node" nodeCount source)
        targetVector
        (← next.decode nodeCount conceptCount roleCount variableCount ontology)
        (← child.decodeAtDepth nodeCount conceptCount roleCount variableCount
          ontology definitions depth)
  | 0, .delay _ => .error "delay node requires positive declared depth"
  | 0, .branch .. => .error "branch node requires positive declared depth"
  | 0, .witness .. => .error "witness node requires positive declared depth"
  | 0, .maximum .. => .error "maximum node requires positive declared depth"
  | 0, .minimum .. => .error "minimum node requires positive declared depth"
  | _ + 1, .equality_apart .. =>
      .error "equality-apart leaf requires declared depth zero"
  | _ + 1, .equality _ => .error "equality leaf requires declared depth zero"
  | _ + 1, .clash => .error "clash leaf requires declared depth zero"

def WireDistinctCardinalityRefutationTree.check
    (nodeCount conceptCount roleCount variableCount depth : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (root : WireDistinctEqState) (wire : WireDistinctCardinalityRefutationTree) :
    Except String Bool := do
  let certificate ← root.decode nodeCount conceptCount roleCount variableCount ontology
  let tree ← wire.decodeAtDepth nodeCount conceptCount roleCount variableCount
    ontology definitions depth
  return tree.checkClosed definitions certificate

structure DecodedDistinctCardinalityRefutation
    (nodeCount conceptCount roleCount variableCount : Nat) where
  depth : Nat
  tree : FiniteDistinctCardinalityRefutationTree
    nodeCount conceptCount roleCount variableCount depth

def WireDistinctCardinalityRefutationTree.decode
    (nodeCount conceptCount roleCount variableCount depth : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (wire : WireDistinctCardinalityRefutationTree) : Except String
      (DecodedDistinctCardinalityRefutation
        nodeCount conceptCount roleCount variableCount) := do
  return ⟨depth, ← wire.decodeAtDepth nodeCount conceptCount roleCount variableCount
    ontology definitions depth⟩

namespace DistinctCardinalityWireTests

private def rootBase : WireEqState where
  labels := [{ node := 0, literal := { concept := 0, neg := false } }]
  edges := []
  obligations := []
  equalities := []
  representatives := [0, 1, 2]
  representative_paths := [[], [], []]

private def root : WireDistinctEqState := { base := rootBase, apart := [] }

private def activeBase : WireEqState where
  labels := [
    { node := 0, literal := { concept := 0, neg := false } },
    { node := 1, literal := { concept := 0, neg := false } },
    { node := 2, literal := { concept := 0, neg := false } }
  ]
  edges := [
    { role := 0, source := 0, target := 1 },
    { role := 0, source := 0, target := 2 }
  ]
  obligations := []
  equalities := []
  representatives := [0, 1, 2]
  representative_paths := [[], [], []]

private def active : WireDistinctEqState where
  base := activeBase
  apart := [{ left := 1, right := 2 }, { left := 2, right := 1 }]

private def merged12 : WireDistinctEqState where
  base := { activeBase with
    equalities := [{ left := 1, right := 2 }]
    representatives := [0, 1, 1]
    representative_paths := [[], [], [1]] }
  apart := active.apart

private def merged21 : WireDistinctEqState where
  base := { activeBase with
    equalities := [{ left := 2, right := 1 }]
    representatives := [0, 1, 1]
    representative_paths := [[], [], [1]] }
  apart := active.apart

private def minimum : CardinalityDef (Fin 1) (Fin 1) :=
  minimumDefinition 0 2 0 0

private def maximum : CardinalityDef (Fin 1) (Fin 1) :=
  maximumDefinition 0 1 0 0

private def tree : WireDistinctCardinalityRefutationTree :=
  .minimum 0 0 [1, 2] active
    (.maximum 1 0 [1, 2] [
      [(active, .equality_apart 1 1), (merged12, .equality_apart 1 2)],
      [(merged21, .equality_apart 2 1), (active, .equality_apart 2 2)]
    ])

example : tree.check 3 1 1 0 2 [] [minimum, maximum] root = .ok true := by
  native_decide

private def oneWayActive : WireDistinctEqState :=
  { active with apart := [{ left := 1, right := 2 }] }

private def badTree : WireDistinctCardinalityRefutationTree :=
  .minimum 0 0 [1, 2] oneWayActive
    (.maximum 1 0 [1, 2] [
      [(active, .equality_apart 1 1), (merged12, .equality_apart 1 2)],
      [(merged21, .equality_apart 2 1), (active, .equality_apart 2 2)]
    ])

example : badTree.check 3 1 1 0 2 [] [minimum, maximum] root = .ok false := by
  native_decide

private def witnessRootBase : WireEqState where
  labels := [
    { node := 0, literal := { concept := 0, neg := false } },
    { node := 0, literal := { concept := 0, neg := true } }
  ]
  edges := []
  obligations := [{ role := 0, filler := { concept := 0, neg := false }, node := 0 }]
  equalities := []
  representatives := [0, 1]
  representative_paths := [[], []]

private def witnessRoot : WireDistinctEqState :=
  { base := witnessRootBase, apart := [] }

private def witnessTree : WireDistinctCardinalityRefutationTree :=
  .witness 0 1 0 { concept := 0, neg := false } .clash

example : witnessTree.check 2 1 1 0 1 [] [] witnessRoot = .ok true := by
  native_decide

private def branchClause : Clause (Fin 1) (Fin 1) (Fin 1) :=
  { body := [], head := [.concept (.pos 0) 0] }

private def branchRootBase : WireEqState where
  labels := [{ node := 0, literal := { concept := 0, neg := true } }]
  edges := []
  obligations := []
  equalities := []
  representatives := [0]
  representative_paths := [[]]

private def branchNextBase : WireEqState :=
  { branchRootBase with
    labels := [
      { node := 0, literal := { concept := 0, neg := false } },
      { node := 0, literal := { concept := 0, neg := true } }
    ] }

private def branchTree : WireDistinctCardinalityRefutationTree :=
  .branch 0 [0] [({ base := branchNextBase, apart := [] }, .clash)]

example : branchTree.check 1 1 1 1 1 [branchClause] []
    { base := branchRootBase, apart := [] } = .ok true := by
  native_decide

end DistinctCardinalityWireTests

end ContextCalculus.Hypertableau
