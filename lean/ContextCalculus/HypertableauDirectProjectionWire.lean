import ContextCalculus.HypertableauWire

/-!
# Checked direct DL-clause to hypertableau projection

This module defines the first fail-closed source-projection certificate used at
the HT boundary.  It covers function-free clauses whose concepts, roles, and
variables are renamed to the finite identifiers consumed by the hypertableau.
The checker resolves every source name itself, rejects duplicate symbol and
variable tables, decodes the claimed target independently, and accepts only
when the complete converted source list is exactly the target ontology.

Existential-function elimination, cardinality replacement, RBox side data,
nominals, and rule compilation require separate proved projection constructors.
They are deliberately not represented by this direct certificate.
-/

namespace ContextCalculus.Hypertableau

open Lean

/-- Function-free source atoms before finite-id assignment. -/
inductive WireDirectSourceAtom where
  | con (concept node : String) (neg : Bool)
  | rol (role source target : String)
  | ex (role filler node : String) (neg : Bool)
  | equal (left right : String)
deriving FromJson, ToJson, Repr

/-- A source clause carries the complete first-occurrence variable table used
to assign its local numeric variables. -/
structure WireDirectSourceClause where
  variableNames : List String
  body : List WireDirectSourceAtom
  head : List WireDirectSourceAtom
deriving FromJson, ToJson, Repr

/-- Complete direct-projection document.  `target` is the exact ontology later
embedded in the HT search certificate. -/
structure WireDirectProjection where
  variable_count : Nat
  concepts : List String
  roles : List String
  source : List WireDirectSourceClause
  target : List WireClause
deriving FromJson, ToJson, Repr

def checkedName : (kind name : String) → (names : List String) →
    Except String (Fin names.length)
  | kind, name, [] => throw s!"unknown {kind} name {name}"
  | kind, name, candidate :: rest =>
      if candidate = name then
        return ⟨0, Nat.zero_lt_succ _⟩
      else
        return Fin.succ (← checkedName kind name rest)

def checkedLocalVariable (variableCount : Nat) (variableNames : List String)
    (name : String) : Except String (Fin variableCount) := do
  if hbound : variableNames.length ≤ variableCount then
    return Fin.castLE hbound (← checkedName "variable" name variableNames)
  else
    throw s!"source clause has {variableNames.length} variables but the target bound is {variableCount}"

def WireDirectSourceAtom.decode (variableCount : Nat)
    (concepts roles variableNames : List String) : WireDirectSourceAtom →
    Except String (Atom (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  | .con concept node neg => do
      return .concept ⟨← checkedName "concept" concept concepts, neg⟩
        (← checkedLocalVariable variableCount variableNames node)
  | .rol role source target => do
      return .role (← checkedName "role" role roles)
        (← checkedLocalVariable variableCount variableNames source)
        (← checkedLocalVariable variableCount variableNames target)
  | .ex role filler node neg => do
      return .exists_ (← checkedName "role" role roles)
        ⟨← checkedName "concept" filler concepts, neg⟩
        (← checkedLocalVariable variableCount variableNames node)
  | .equal left right => do
      return .eq (← checkedLocalVariable variableCount variableNames left)
        (← checkedLocalVariable variableCount variableNames right)

def WireDirectSourceClause.decode (variableCount : Nat)
    (concepts roles : List String) (wire : WireDirectSourceClause) :
    Except String (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length)) := do
  if wire.variableNames.Nodup then
    return {
      body := ← wire.body.mapM
        (WireDirectSourceAtom.decode variableCount concepts roles wire.variableNames)
      head := ← wire.head.mapM
        (WireDirectSourceAtom.decode variableCount concepts roles wire.variableNames)
    }
  else
    throw "source clause variable table contains duplicates"

structure DecodedDirectProjection where
  variableCount : Nat
  concepts : List String
  roles : List String
  source : List (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  target : List (Clause (Fin variableCount) (Fin concepts.length) (Fin roles.length))
  exact_projection : source = target

def WireDirectProjection.decode (wire : WireDirectProjection) :
    Except String DecodedDirectProjection := do
  if _hconcepts : wire.concepts.Nodup then
    if _hroles : wire.roles.Nodup then
      let source ← wire.source.mapM
        (WireDirectSourceClause.decode wire.variable_count wire.concepts wire.roles)
      let target ← wire.target.mapM
        (WireClause.decode wire.variable_count wire.concepts.length wire.roles.length)
      if hequal : source = target then
        return {
          variableCount := wire.variable_count
          concepts := wire.concepts
          roles := wire.roles
          source
          target
          exact_projection := hequal
        }
      else
        throw "direct source conversion differs from the claimed HT ontology"
    else
      throw "HT role-name table contains duplicates"
  else
    throw "HT concept-name table contains duplicates"

def WireDirectProjection.check (wire : WireDirectProjection) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedDirectProjection.models_source_iff_target
    (decoded : DecodedDirectProjection)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length)) :
    I.models decoded.source ↔ I.models decoded.target := by
  rw [decoded.exact_projection]

theorem WireDirectProjection.check_sound (wire : WireDirectProjection)
    (decoded : DecodedDirectProjection) (_hdecode : wire.decode = .ok decoded)
    (_hcheck : wire.check = .ok true)
    (I : Interp Domain (Fin decoded.concepts.length) (Fin decoded.roles.length)) :
    I.models decoded.source ↔ I.models decoded.target := by
  exact decoded.models_source_iff_target I

section Tests

private def directExample : WireDirectProjection where
  variable_count := 2
  concepts := ["A", "B"]
  roles := ["r"]
  source := [{
    variableNames := ["x", "y"]
    body := [.con "A" "x" false, .rol "r" "x" "y"]
    head := [.con "B" "y" false]
  }]
  target := [{
    body := [
      .concept { concept := 0, neg := false } 0,
      .role 0 0 1]
    head := [.concept { concept := 1, neg := false } 1]
  }]

example : directExample.check = .ok true := by native_decide

private def omittedTarget : WireDirectProjection :=
  { directExample with target := [] }

private def rejected (result : Except String Bool) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

example : rejected omittedTarget.check = true := by native_decide

private def forgedTarget : WireDirectProjection :=
  { directExample with target := [{
      body := [.concept { concept := 0, neg := false } 0]
      head := [.concept { concept := 1, neg := false } 1]
    }] }

example : rejected forgedTarget.check = true := by native_decide

private def duplicateConcepts : WireDirectProjection :=
  { directExample with concepts := ["A", "A", "B"] }

example : rejected duplicateConcepts.check = true := by native_decide

#print axioms DecodedDirectProjection.models_source_iff_target
#print axioms WireDirectProjection.check_sound

end Tests

end ContextCalculus.Hypertableau
