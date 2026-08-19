import ContextCalculus.HypertableauPreprocessing
import ContextCalculus.HypertableauWire
import ContextCalculus.HypertableauEqualityNormalizationWire

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

structure WireContrapositive where
  source_clause : Nat
  node : Nat
  selected : WireLit
  left_literals : List WireLit
  right_literals : List WireLit
deriving FromJson, ToJson, Repr

def decodeLitList (conceptCount : Nat) (values : List WireLit) :
    Except String (List (Lit (Fin conceptCount))) :=
  values.mapM (WireLit.decode conceptCount)

structure DecodedContrapositiveExtension
    (base : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) where
  added : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  proof : ContrapositiveExtension base added

def decodeContrapositives (variableCount conceptCount roleCount : Nat)
    (base : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) : List WireContrapositive →
    Except String (DecodedContrapositiveExtension base)
  | [] => return ⟨[], ⟨by
      intro target member
      simp at member⟩⟩
  | wire :: wires => do
      let sourceIndex ← checkedFin "source clause" base.length wire.source_clause
      let source := base.get sourceIndex
      let node ← checkedFin "variable" variableCount wire.node
      let selected ← wire.selected.decode conceptCount
      let leftLits ← decodeLitList conceptCount wire.left_literals
      let rightLits ← decodeLitList conceptCount wire.right_literals
      let expectedSource : Clause (Fin variableCount) (Fin conceptCount)
          (Fin roleCount) := {
        body := conceptAtoms node (leftLits ++ selected :: rightLits)
        head := [] }
      let target : Clause (Fin variableCount) (Fin conceptCount)
          (Fin roleCount) := {
        body := conceptAtoms node (leftLits ++ rightLits)
        head := [.concept selected.complement node] }
      if hsource : source = expectedSource then
        let tail ← decodeContrapositives variableCount conceptCount roleCount base wires
        let derivation : ClashContrapositive source target := {
          node
          selected
          leftLits
          rightLits
          source_eq := hsource
          target_eq := rfl
        }
        let headWitness : ContrapositiveWitness base target :=
          .intro source (List.get_mem base sourceIndex) derivation
        let extension : ContrapositiveExtension base (target :: tail.added) := {
          witness := by
            intro clause member
            rcases List.mem_cons.mp member with equal | rest
            · exact equal ▸ headWitness
            · exact tail.proof.witness clause rest
        }
        return ⟨target :: tail.added, extension⟩
      else
        throw "contrapositive source does not match its checked clash split"

/-- Untrusted source and intermediate data for the two optional preprocessing
passes. Equality normalization remains in its existing wire field, allowing the
composed decoder to check all three stages against the final certificate
ontology. -/
structure WirePreprocessingEvidence where
  source : List WireClause
  absorbed : List WireClause
  trigger_steps : List WireTriggerStep
  contrapositives : List WireContrapositive
deriving FromJson, ToJson, Repr

structure DecodedPreprocessing
    (target : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) where
  source : List (Clause (Fin variableCount) (Fin conceptCount) (Fin roleCount))
  proof : PreprocessingCertificate source target

def WirePreprocessingEvidence.decode
    (wire : WirePreprocessingEvidence)
    (variableCount conceptCount roleCount : Nat)
    (normalization : List WireClauseNormalization)
    (target : List (Clause (Fin variableCount) (Fin conceptCount)
      (Fin roleCount))) : Except String (DecodedPreprocessing target) := do
  let equality ← decodeOntologyNormalization variableCount conceptCount roleCount
    normalization target
  let source ← decodeWireClauses variableCount conceptCount roleCount wire.source
  let absorbed ← decodeWireClauses variableCount conceptCount roleCount wire.absorbed
  let trigger ← decodeTriggerPass variableCount conceptCount roleCount source absorbed
    wire.trigger_steps
  let contra ← decodeContrapositives variableCount conceptCount roleCount absorbed
    wire.contrapositives
  if hpreprocessed : equality.source = absorbed ++ contra.added then
    let equalityProof : OntologyEqualityNormalization
        (absorbed ++ contra.added) target := hpreprocessed ▸ equality.proof
    return ⟨source, {
      absorbed
      added := contra.added
      trigger := trigger.proof
      contra := contra.proof
      equality := equalityProof
    }⟩
  else
    throw "checked preprocessing output does not match equality-normalization input"

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

private def allNegativeSource : WireClause where
  body := []
  head := [
    .concept { concept := 0, neg := true } 0,
    .concept { concept := 1, neg := true } 0]

private def absorbedClash : WireClause where
  body := [
    .concept { concept := 0, neg := false } 0,
    .concept { concept := 1, neg := false } 0]
  head := []

private def contraNotZero : WireClause where
  body := [.concept { concept := 1, neg := false } 0]
  head := [.concept { concept := 0, neg := true } 0]

private def contraNotOne : WireClause where
  body := [.concept { concept := 0, neg := false } 0]
  head := [.concept { concept := 1, neg := true } 0]

private def identityNormalization (source : WireClause) : WireClauseNormalization where
  source
  representatives := [0]
  representative_paths := [[0]]

private def completePreprocessingWire : WirePreprocessingEvidence where
  source := [allNegativeSource]
  absorbed := [absorbedClash]
  trigger_steps := [.absorb 0 [0, 1] []]
  contrapositives := [
    {
      source_clause := 0
      node := 0
      selected := { concept := 0, neg := false }
      left_literals := []
      right_literals := [{ concept := 1, neg := false }]
    },
    {
      source_clause := 0
      node := 0
      selected := { concept := 1, neg := false }
      left_literals := [{ concept := 0, neg := false }]
      right_literals := []
    }]

example : (do
    let target ← decodeWireClauses 1 2 0
      [absorbedClash, contraNotZero, contraNotOne]
    let _ ← completePreprocessingWire.decode 1 2 0 [
      identityNormalization absorbedClash,
      identityNormalization contraNotZero,
      identityNormalization contraNotOne] target
    return true) = .ok true := by
  native_decide

example : (do
    let target ← decodeWireClauses 1 2 0 [absorbedClash]
    let result := completePreprocessingWire.decode 1 2 0
      [identityNormalization absorbedClash] target
    return rejected result) = .ok true := by
  native_decide

private def clashSource : WireClause where
  body := [
    .concept { concept := 0, neg := false } 0,
    .concept { concept := 1, neg := false } 0,
    .concept { concept := 2, neg := true } 0]
  head := []

private def expectedContrapositive : WireClause where
  body := [
    .concept { concept := 0, neg := false } 0,
    .concept { concept := 2, neg := true } 0]
  head := [.concept { concept := 1, neg := true } 0]

private def validContrapositive : WireContrapositive where
  source_clause := 0
  node := 0
  selected := { concept := 1, neg := false }
  left_literals := [{ concept := 0, neg := false }]
  right_literals := [{ concept := 2, neg := true }]

example : (do
    let base ← decodeWireClauses 1 3 0 [clashSource]
    let expected ← decodeWireClauses 1 3 0 [expectedContrapositive]
    let decoded ← decodeContrapositives 1 3 0 base [validContrapositive]
    return decoded.added == expected) = .ok true := by
  native_decide

example : (do
    let base ← decodeWireClauses 1 3 0 [clashSource]
    let forged := { validContrapositive with source_clause := 1 }
    let result := decodeContrapositives 1 3 0 base [forged]
    return rejected result) = .ok true := by
  native_decide

example : (do
    let base ← decodeWireClauses 1 3 0 [clashSource]
    let forged := { validContrapositive with
      right_literals := [{ concept := 0, neg := true }] }
    let result := decodeContrapositives 1 3 0 base [forged]
    return rejected result) = .ok true := by
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
#print axioms decodeContrapositives
#print axioms WirePreprocessingEvidence.decode

end ContextCalculus.Hypertableau
