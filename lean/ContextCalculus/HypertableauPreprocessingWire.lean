import ContextCalculus.HypertableauPreprocessing
import ContextCalculus.HypertableauWire

/-!
# Executable wire checker for HT trigger absorption

The wire records one decision for every source clause. The checker independently
decodes all identifiers, checks unchanged clauses by equality, and checks an
absorbed clause against the exact positive/negative partition supplied by the
producer. It returns the semantic proof object from
`HypertableauPreprocessing`, rather than a Boolean assertion supplied by Rust.
-/

namespace ContextCalculus.Hypertableau

open Lean

inductive WireTriggerStep where
  | keep
  | absorb (node : Nat) (negative positive : List Nat)
deriving FromJson, ToJson, Repr

structure CheckedTriggerClause
    (source target : Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount)) where
  proof : TriggerAbsorption source target

def decodeConceptList (conceptCount : Nat) (values : List Nat) :
    Except String (List (Fin conceptCount)) :=
  values.mapM (checkedFin "concept" conceptCount)

def WireTriggerStep.decodeAbsorption
    (nodeValue : Nat) (negativeValues positiveValues : List Nat)
    (variableCount conceptCount roleCount : Nat)
    (source target : Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount)) : Except String (CheckedTriggerClause source target) := do
  let node ← checkedFin "variable" variableCount nodeValue
  let negative ← decodeConceptList conceptCount negativeValues
  let positive ← decodeConceptList conceptCount positiveValues
  let expectedHead :=
    negativeConceptAtoms node negative ++ positiveConceptAtoms node positive
  let expectedTarget : Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount) := {
    body := positiveConceptAtoms node negative
    head := positiveConceptAtoms node positive }
  if hbody : source.body = [] then
    if hhead : source.head.Perm expectedHead then
      if htarget : target = expectedTarget then
        return ⟨{
          node
          negative
          positive
          source_body := hbody
          source_head := hhead
          target_eq := htarget
        }⟩
      else
        throw "absorbed target does not match its checked literal partition"
    else
      throw "source head does not match its checked literal partition"
  else
    throw "an absorbed source clause must have an empty body"

structure CheckedTriggerPass
    (source target : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) where
  marker : Unit
  proof : OntologyTriggerAbsorption source target

def decodeTriggerPass (variableCount conceptCount roleCount : Nat) :
    (source target : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) → List WireTriggerStep →
    Except String (CheckedTriggerPass source target)
  | [], [], [] => return ⟨(), .nil⟩
  | sourceClause :: sources, targetClause :: targets, step :: steps => do
      let tail ← decodeTriggerPass variableCount conceptCount roleCount sources targets steps
      match step with
      | .keep =>
          if hequal : sourceClause = targetClause then
            return ⟨(), hequal ▸ .keep tail.proof⟩
          else
            throw "kept trigger clause differs from its source"
      | .absorb node negative positive =>
          let head ← WireTriggerStep.decodeAbsorption node negative positive
            variableCount conceptCount roleCount sourceClause targetClause
          return ⟨(), .absorb head.proof tail.proof⟩
  | _, _, _ => throw "trigger-step count does not match source and target ontologies"

def decodeWireClauses (variableCount conceptCount roleCount : Nat)
    (clauses : List WireClause) : Except String
      (List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))) :=
  clauses.mapM (WireClause.decode variableCount conceptCount roleCount)

section Tests

private def mixedSource : WireClause where
  body := []
  head := [
    .concept { concept := 0, neg := false } 0,
    .concept { concept := 1, neg := true } 0,
    .concept { concept := 2, neg := false } 0]

private def mixedTarget : WireClause where
  body := [.concept { concept := 1, neg := false } 0]
  head := [
    .concept { concept := 0, neg := false } 0,
    .concept { concept := 2, neg := false } 0]

private def rejected {α : Type} : Except String α → Bool
  | .error _ => true
  | .ok _ => false

example : (do
    let source ← decodeWireClauses 1 3 0 [mixedSource]
    let target ← decodeWireClauses 1 3 0 [mixedTarget]
    let _ ← decodeTriggerPass 1 3 0 source target [.absorb 0 [1] [0, 2]]
    return true) = .ok true := by
  native_decide

example : (do
    let source ← decodeWireClauses 1 3 0 [mixedSource]
    let target ← decodeWireClauses 1 3 0 [mixedTarget]
    let result := decodeTriggerPass 1 3 0 source target [.absorb 0 [0] [1, 2]]
    return rejected result) = .ok true := by
  native_decide

example : (do
    let source ← decodeWireClauses 1 3 0 [mixedSource]
    let target ← decodeWireClauses 1 3 0 [mixedTarget]
    let result := decodeTriggerPass 1 3 0 source target []
    return rejected result) = .ok true := by
  native_decide

end Tests

#print axioms decodeTriggerPass

end ContextCalculus.Hypertableau
