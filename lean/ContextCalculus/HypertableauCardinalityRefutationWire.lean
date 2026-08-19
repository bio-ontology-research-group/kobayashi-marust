import ContextCalculus.HypertableauCardinalityRefutationCertificate
import ContextCalculus.HypertableauEqualityWire
import Lean

/-!
# Wire format for cardinality-aware HT refutations

The declared depth is checked structurally.  Maximum children form a flattened
row-major square with exactly `(bound + 1)²` entries.  Every node, definition,
and child state is bounds checked before construction of the proved checker.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireCardinalityEqRefutationTree where
  | equality (tree : WireEqRefutationTree)
  | clash
  | delay (child : WireCardinalityEqRefutationTree)
  | branch (clause : Nat) (assignment : List Nat)
      (children : List (WireEqState × WireCardinalityEqRefutationTree))
  | witness (source target role : Nat) (filler : WireLit)
      (child : WireCardinalityEqRefutationTree)
  | maximum (definition source : Nat) (witnesses : List Nat)
      (children : List (List (WireEqState × WireCardinalityEqRefutationTree)))
deriving FromJson, ToJson, Repr

def decodeExactVector (kind : String) (expected : Nat) (values : List α) :
    Except String (Fin expected → α) :=
  if h : values.length = expected then
    .ok fun index => values.get (h.symm ▸ index)
  else
    .error s!"{kind} has {values.length} entries, expected {expected}"

def WireCardinalityEqRefutationTree.decodeAtDepth
    (nodeCount conceptCount roleCount variableCount : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount))) :
    (depth : Nat) → WireCardinalityEqRefutationTree → Except String
      (FiniteCardinalityEqRefutationTree
        nodeCount conceptCount roleCount variableCount depth)
  | 0, .equality tree => do
      return .equality (← tree.decode nodeCount conceptCount roleCount variableCount ontology)
  | 0, .clash => return .clash
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
        decodeExactVector "maximum child row" width decodedRow
      let childMatrix ← decodeExactVector "maximum child rows" width decodedRows
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
      let childVector ← decodeExactVector "cardinality branch children"
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
  | 0, .delay _ => .error "delay node requires positive declared depth"
  | 0, .branch .. => .error "branch node requires positive declared depth"
  | 0, .witness .. => .error "witness node requires positive declared depth"
  | 0, .maximum .. => .error "maximum node requires positive declared depth"
  | _ + 1, .equality _ => .error "equality leaf requires declared depth zero"
  | _ + 1, .clash => .error "clash leaf requires declared depth zero"

structure DecodedCardinalityEqRefutation
    (nodeCount conceptCount roleCount variableCount : Nat) where
  depth : Nat
  tree : FiniteCardinalityEqRefutationTree
    nodeCount conceptCount roleCount variableCount depth

def WireCardinalityEqRefutationTree.decode
    (nodeCount conceptCount roleCount variableCount depth : Nat)
    (ontology : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount)))
    (definitions : List (CardinalityDef (Fin conceptCount) (Fin roleCount)))
    (wire : WireCardinalityEqRefutationTree) : Except String
      (DecodedCardinalityEqRefutation nodeCount conceptCount roleCount variableCount) := do
  return ⟨depth, ← wire.decodeAtDepth nodeCount conceptCount roleCount variableCount
    ontology definitions depth⟩

namespace CardinalityRefutationWireTests

private def equalityLeaf : WireCardinalityEqRefutationTree := .equality .clash

private def isError {ε α : Type} : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

example : isError (equalityLeaf.decodeAtDepth 1 1 1 0 [] [] 1) = true := by
  native_decide

end CardinalityRefutationWireTests

end ContextCalculus.Hypertableau
