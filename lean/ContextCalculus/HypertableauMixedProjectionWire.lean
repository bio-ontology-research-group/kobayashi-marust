import ContextCalculus.HypertableauDirectProjectionWire
import ContextCalculus.HypertableauSkolemProjection
import Mathlib.Data.Finset.Basic

/-!
# Mixed direct and Skolem-pair projection wire

This decoder extends the direct HT projection boundary with exact common-body
unary Skolem pairs.  It resolves every name independently, rejects duplicate
symbol and function tables, and compares the complete projected ontology with
the actual HT target modulo order and duplicate clauses.  Clause order and
duplicate copies do not affect `Interp.models`.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireSkolemPair where
  variableNames : List String
  body : List WireDirectSourceAtom
  source : String
  function : String
  role : String
  filler : String
  neg : Bool
deriving FromJson, ToJson, Repr

def WireSkolemPair.decode (variableCount : Nat)
    (concepts roles functions : List String) (wire : WireSkolemPair) :
    Except String
      (SkolemPairSpec (Fin variableCount) (Fin concepts.length)
        (Fin roles.length) (Fin functions.length)) := do
  if wire.variableNames.Nodup then
    return {
      body := ← wire.body.mapM
        (WireDirectSourceAtom.decode variableCount concepts roles wire.variableNames)
      source := ← checkedLocalVariable variableCount wire.variableNames wire.source
      function := ← checkedName "function" wire.function functions
      role := ← checkedName "role" wire.role roles
      filler := {
        concept := ← checkedName "concept" wire.filler concepts
        neg := wire.neg
      }
    }
  else
    throw "Skolem pair variable table contains duplicates"

structure WireMixedProjection where
  variable_count : Nat
  concepts : List String
  roles : List String
  functions : List String
  direct : List WireDirectSourceClause
  pairs : List WireSkolemPair
  target : List WireClause
deriving FromJson, ToJson, Repr

structure DecodedMixedProjection where
  variableCount : Nat
  concepts : List String
  roles : List String
  functions : List String
  direct : List
    (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  pairs : List
    (SkolemPairSpec (Fin variableCount) (Fin concepts.length)
      (Fin roles.length) (Fin functions.length))
  target : List
    (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  uniqueFunctions : (skolemPairFunctions pairs).Nodup
  exactProjection :
    (skolemProjectionOntology direct pairs).toFinset = target.toFinset

def WireMixedProjection.decode (wire : WireMixedProjection) :
    Except String DecodedMixedProjection := do
  if _hconcepts : wire.concepts.Nodup then
    if _hroles : wire.roles.Nodup then
      if _hfunctions : wire.functions.Nodup then
        let direct ← wire.direct.mapM
          (WireDirectSourceClause.decode wire.variable_count wire.concepts wire.roles)
        let pairs ← wire.pairs.mapM
          (WireSkolemPair.decode wire.variable_count wire.concepts wire.roles wire.functions)
        let target ← wire.target.mapM
          (WireClause.decode wire.variable_count wire.concepts.length wire.roles.length)
        if hunique : (skolemPairFunctions pairs).Nodup then
          if hequal : (skolemProjectionOntology direct pairs).toFinset = target.toFinset then
            return {
              variableCount := wire.variable_count
              concepts := wire.concepts
              roles := wire.roles
              functions := wire.functions
              direct
              pairs
              target
              uniqueFunctions := hunique
              exactProjection := hequal
            }
          else
            throw "mixed source conversion differs from the claimed HT ontology"
        else
          throw "mixed projection reuses a Skolem function"
      else
        throw "HT function-name table contains duplicates"
    else
      throw "HT role-name table contains duplicates"
  else
    throw "HT concept-name table contains duplicates"

def WireMixedProjection.check (wire : WireMixedProjection) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem models_iff_of_toFinset_eq
    [DecidableEq Variable] [DecidableEq Concept] [DecidableEq Role]
    (I : Interp Domain Concept Role)
    (left right : List (Clause Variable Concept Role))
    (hequal : left.toFinset = right.toFinset) :
    I.models left ↔ I.models right := by
  constructor
  · intro hmodels clause hclause
    apply hmodels clause
    have : clause ∈ right.toFinset := by simpa using hclause
    rw [← hequal] at this
    simpa using this
  · intro hmodels clause hclause
    apply hmodels clause
    have : clause ∈ left.toFinset := by simpa using hclause
    rw [hequal] at this
    simpa using this

theorem DecodedMixedProjection.models_source_iff_target
    (decoded : DecodedMixedProjection)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (base : SkolemInterp Domain (Fin decoded.functions.length)) :
    (∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
      I.models decoded.direct ∧ ModelsSkolemPairs I functions decoded.pairs) ↔
      I.models decoded.target := by
  rw [mixedSkolemProjection_sat_iff I base decoded.direct decoded.pairs
    decoded.uniqueFunctions]
  exact models_iff_of_toFinset_eq I _ _ decoded.exactProjection

theorem WireMixedProjection.check_sound (wire : WireMixedProjection)
    (decoded : DecodedMixedProjection) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length))
    (base : SkolemInterp Domain (Fin decoded.functions.length)) :
    (∃ functions : SkolemInterp Domain (Fin decoded.functions.length),
      I.models decoded.direct ∧ ModelsSkolemPairs I functions decoded.pairs) ↔
      I.models decoded.target := by
  exact decoded.models_source_iff_target I base

section Tests

private def mixedExample : WireMixedProjection where
  variable_count := 1
  concepts := ["A", "B", "C"]
  roles := ["r"]
  functions := ["f"]
  direct := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    head := [.con "B" "x" false]
  }]
  pairs := [{
    variableNames := ["x"]
    body := [.con "A" "x" false]
    source := "x"
    function := "f"
    role := "r"
    filler := "C"
    neg := false
  }]
  target := [
    {
      body := [.concept { concept := 0, neg := false } 0]
      head := [.exists_ 0 { concept := 2, neg := false } 0]
    },
    {
      body := [.concept { concept := 0, neg := false } 0]
      head := [.concept { concept := 1, neg := false } 0]
    }
  ]

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : mixedExample.check = .ok true := by native_decide

example : rejected ({ mixedExample with target := mixedExample.target.drop 1 }).check = true := by
  native_decide

example : rejected ({ mixedExample with pairs := mixedExample.pairs ++ mixedExample.pairs }).check = true := by
  native_decide

#print axioms models_iff_of_toFinset_eq
#print axioms DecodedMixedProjection.models_source_iff_target
#print axioms WireMixedProjection.check_sound

end Tests

end ContextCalculus.Hypertableau
