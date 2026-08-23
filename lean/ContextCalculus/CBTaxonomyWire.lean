import ContextCalculus.CBFiniteModelWire

/-!
# Exact source-bound CB taxonomy publication

One document owns the normalized CB ontology and symbol bounds.  It lists a
row-major square matrix over the named concepts.  Every true cell carries a
checked nested-term derivation, while every false cell carries a checked finite
countermodel.  The decoder checks matrix shape, coordinates, and published
bits, preventing evidence from one source or query from being reused for
another.
-/

namespace ContextCalculus.CBTaxonomyWire

open Lean ContextCalculus CheckerTerm CBFiniteModelWire
open ContextCalculus.CBTermWire

def Entails (ontology : List FCL) (core superconcept : Nat) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ ontology, valid model clause) →
    ∀ element, model.conc core element → model.conc superconcept element

inductive WireCellEvidence where
  | positive (trace : List WireEntry)
  | negative (witness : Nat) (model : WireFiniteModel)
deriving FromJson, ToJson

structure WireCell where
  core_concept : Nat
  superconcept : Nat
  answer : Bool
  evidence : WireCellEvidence
deriving FromJson, ToJson

structure DecodedCell (bounds : Bounds) (ontology : List FCL) where
  coreConcept : Nat
  superconcept : Nat
  answer : Bool
  exact : answer = true ↔ Entails ontology coreConcept superconcept

def WireCell.decode (bounds : Bounds) (ontology : List FCL)
    (wire : WireCell) : Except String (DecodedCell bounds ontology) := do
  let core ← checkId "taxonomy core concept" bounds.concepts wire.core_concept
  let superconcept ← checkId "taxonomy superconcept" bounds.concepts wire.superconcept
  match wire.evidence with
  | .positive wireTrace =>
      if wire.answer != true then
        throw "positive CB taxonomy evidence is paired with a false answer"
      let trace ← wireTrace.mapM (WireEntry.decode bounds)
      let document : DecodedDocument := {
        ontology
        coreConcept := core
        verdict := .subsumption superconcept
        trace
      }
      if hcheck : document.check = true then
        have hsemantic : Entails ontology core superconcept := by
          simpa [Entails, document] using document.check_sound hcheck
        return {
          coreConcept := core
          superconcept
          answer := true
          exact := ⟨fun _ => hsemantic, fun _ => rfl⟩
        }
      else throw "positive CB taxonomy derivation was rejected"
  | .negative witness model =>
      if wire.answer != false then
        throw "negative CB taxonomy evidence is paired with a true answer"
      let countermodelWire : WireCountermodel := {
        core_concept := core
        superconcept
        witness
        model
      }
      let countermodel ← countermodelWire.decode bounds ontology
      have hnot : ¬Entails ontology countermodel.coreConcept
          countermodel.superconcept := countermodel.refutes_subsumption
      return {
        coreConcept := countermodel.coreConcept
        superconcept := countermodel.superconcept
        answer := false
        exact := ⟨by simp, fun hentails => (hnot hentails).elim⟩
      }

structure WireTaxonomy where
  version : Nat
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  ontology : List WireClause
  named_concepts : List Nat
  published : List Bool
  cells : List WireCell
deriving FromJson, ToJson

def WireTaxonomy.bounds (wire : WireTaxonomy) : Bounds :=
  { concepts := wire.concept_count
  , roles := wire.role_count
  , functions := wire.function_count
  , individuals := wire.individual_count }

def coordinates (named : List Nat) : List (Nat × Nat) :=
  named.flatMap fun core => named.map fun superconcept => (core, superconcept)

structure DecodedTaxonomy where
  bounds : Bounds
  ontology : List FCL
  named : List Nat
  cells : List (DecodedCell bounds ontology)
  exact_coordinates : cells.map (fun cell =>
    (cell.coreConcept, cell.superconcept)) = coordinates named

def WireTaxonomy.decode (wire : WireTaxonomy) : Except String DecodedTaxonomy := do
  if wire.version != 1 then
    throw s!"unsupported CB taxonomy certificate version {wire.version}"
  if wire.concept_count = 0 then
    throw "concept_count must be positive"
  let bounds := wire.bounds
  let ontology ← wire.ontology.mapM (WireClause.decode bounds)
  if _hnamed : wire.named_concepts.Nodup then
    let named ← wire.named_concepts.mapM
      (checkId "named taxonomy concept" bounds.concepts)
    let cells ← wire.cells.mapM (WireCell.decode bounds ontology)
    if hcoordinates : cells.map (fun cell =>
        (cell.coreConcept, cell.superconcept)) = coordinates named then
      if _hanswers : cells.map (·.answer) = wire.published then
        return {
          bounds
          ontology
          named
          cells
          exact_coordinates := hcoordinates
        }
      else throw "CB taxonomy publication bits differ from their checked evidence"
    else throw "CB taxonomy cells do not form the complete named-concept matrix"
  else throw "CB taxonomy named concept table contains duplicates"

def DecodedTaxonomy.published (decoded : DecodedTaxonomy) : List Bool :=
  decoded.cells.map (·.answer)

def WireTaxonomy.check (wire : WireTaxonomy) : Except String Bool := do
  let _ ← wire.decode
  return true

/-- Every published flat matrix entry is exactly the semantic answer for its
checked row-major coordinate. -/
theorem DecodedTaxonomy.publishes_exactly (decoded : DecodedTaxonomy)
    (index : Fin decoded.cells.length) :
    decoded.published.get
      ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
      Entails decoded.ontology
        (decoded.cells.get index).coreConcept
        (decoded.cells.get index).superconcept := by
  have hanswer : decoded.published.get
      ⟨index, by simp [DecodedTaxonomy.published]⟩ =
      (decoded.cells.get index).answer := by
    simp [DecodedTaxonomy.published]
  rw [hanswer]
  exact (decoded.cells.get index).exact

theorem WireTaxonomy.check_sound (wire : WireTaxonomy)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedTaxonomy,
      wire.decode = .ok decoded ∧
        ∀ index : Fin decoded.cells.length,
          decoded.published.get
            ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
          Entails decoded.ontology
            (decoded.cells.get index).coreConcept
            (decoded.cells.get index).superconcept := by
  cases hdecode : wire.decode with
  | error message => simp [WireTaxonomy.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.publishes_exactly⟩

private def x : WireTerm := .var 0
private def concept (id : Nat) : WireLiteral := .predicate (.concept id x)
private def positiveCell (id : Nat) : WireCell := {
  core_concept := id
  superconcept := id
  answer := true
  evidence := .positive [⟨⟨[], [concept id]⟩, .core⟩]
}
private def negativeCell (core superconcept : Nat) : WireCell := {
  core_concept := core
  superconcept
  answer := false
  evidence := .negative 0 {
    domain_size := 1
    concepts := if core = 0 then [[true], [false]] else [[false], [true]]
    roles := []
    constants := []
    functions := []
  }
}
private def exactExample : WireTaxonomy := {
  version := 1
  concept_count := 2
  role_count := 0
  function_count := 0
  individual_count := 0
  ontology := []
  named_concepts := [0, 1]
  published := [true, false, false, true]
  cells := [positiveCell 0, negativeCell 0 1,
    negativeCell 1 0, positiveCell 1]
}
private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : exactExample.check = .ok true := by native_decide
example : rejected ({ exactExample with cells := exactExample.cells.drop 1 }).check = true := by
  native_decide
example : rejected ({ exactExample with published := [true, true, false, true] }).check = true := by
  native_decide

#print axioms DecodedTaxonomy.publishes_exactly
#print axioms WireTaxonomy.check_sound

end ContextCalculus.CBTaxonomyWire
