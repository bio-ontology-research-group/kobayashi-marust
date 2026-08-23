import ContextCalculus.CBFiniteModelWire
import ContextCalculus.CBProductionTraceWire
import ContextCalculus.CBRegularArbitraryChainCountermodelWire
import Mathlib.Data.Finset.Basic

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
open ContextCalculus.CBProductionTrace ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBRegularArbitraryChainCountermodelWire

def Entails (ontology : List FCL) (core superconcept : Nat) : Prop :=
  ∀ (D : Type) (model : TModel D),
    (∀ clause ∈ ontology, valid model clause) →
    ∀ element, model.conc core element → model.conc superconcept element

inductive WireCellEvidence where
  | positive (trace : List WireEntry)
  | positiveProduction (trace : List WireProductionEntry)
  | negative (witness : Nat) (model : WireFiniteModel)
  | regularArbitraryChain (model : WireRegularArbitraryChainCountermodel)
deriving FromJson, ToJson

structure WireCell where
  core_concept : Nat
  superconcept : Nat
  answer : Bool
  evidence : WireCellEvidence
deriving FromJson, ToJson

structure WireSubsumption where
  sub : String
  sup : String
deriving DecidableEq, FromJson, ToJson, Repr

structure DecodedCell (bounds : Bounds) (ontology : List FCL) where
  coreConcept : Nat
  core_in_bounds : coreConcept < bounds.concepts
  superconcept : Nat
  super_in_bounds : superconcept < bounds.concepts
  answer : Bool
  exact : answer = true ↔ Entails ontology coreConcept superconcept

def WireCell.decode (bounds : Bounds) (ontology : List FCL)
    (wire : WireCell) : Except String (DecodedCell bounds ontology) := do
  let core ← checkId "taxonomy core concept" bounds.concepts wire.core_concept
  let superconcept ← checkId "taxonomy superconcept" bounds.concepts wire.superconcept
  if hcore : core < bounds.concepts then
    if hsuper : superconcept < bounds.concepts then
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
          core_in_bounds := hcore
          superconcept
          super_in_bounds := hsuper
          answer := true
          exact := ⟨fun _ => hsemantic, fun _ => rfl⟩
        }
      else throw "positive CB taxonomy derivation was rejected"
  | .positiveProduction wireTrace =>
      if wire.answer != true then
        throw "production CB taxonomy evidence is paired with a false answer"
      let queryPredicate : WirePredicate := .concept core (.var 0)
      let contextWire : WireProductionContext := {
        context_id := 0
        root := true
        nominal_ground := false
        query_concept := some core
        core := [queryPredicate]
        retained := wireTrace.map (·.clause)
        discarded := []
        trace := wireTrace
      }
      let context ← contextWire.decode bounds ontology
      let target : FCL :=
        ⟨[], [.P (.concept superconcept (.var 0))]⟩
      if hcoreExact : context.core = [.concept core (.var 0)] then
        if htarget : target ∈ context.retained then
          have hsemantic : Entails ontology core superconcept := by
            intro D model hontology element hsub
            let assignment : Int → D := fun _ => element
            have hcore : CoreHolds model assignment context.core := by
              rw [hcoreExact]
              intro predicate hpredicate
              simp only [List.mem_singleton] at hpredicate
              subst predicate
              exact hsub
            have hvalid := context.retained_sound model assignment hontology
              hcore target htarget
            have hhead := hvalid (by intro literal hliteral; cases hliteral)
            obtain ⟨literal, hliteral, heval⟩ := hhead
            simp only [target, List.mem_singleton] at hliteral
            subst literal
            exact heval
          return {
            coreConcept := core
            core_in_bounds := hcore
            superconcept
            super_in_bounds := hsuper
            answer := true
            exact := ⟨fun _ => hsemantic, fun _ => rfl⟩
          }
        else
          let bottom : FCL := ⟨[], []⟩
          if hbottom : bottom ∈ context.retained then
            have hsemantic : Entails ontology core superconcept := by
              intro D model hontology element hsub
              let assignment : Int → D := fun _ => element
              have hcore : CoreHolds model assignment context.core := by
                rw [hcoreExact]
                intro predicate hpredicate
                simp only [List.mem_singleton] at hpredicate
                subst predicate
                exact hsub
              have hvalid := context.retained_sound model assignment hontology
                hcore bottom hbottom
              have hfalse := hvalid (by intro literal hliteral; cases hliteral)
              obtain ⟨literal, hliteral, _⟩ := hfalse
              cases hliteral
            return {
              coreConcept := core
              core_in_bounds := hcore
              superconcept
              super_in_bounds := hsuper
              answer := true
              exact := ⟨fun _ => hsemantic, fun _ => rfl⟩
            }
          else throw "production CB taxonomy trace omits its target unit or contradiction"
      else throw "production CB taxonomy trace uses the wrong query core"
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
        core_in_bounds := countermodel.core_in_bounds
        superconcept := countermodel.superconcept
        super_in_bounds := countermodel.super_in_bounds
        answer := false
        exact := ⟨by simp, fun hentails => (hnot hentails).elim⟩
      }
  | .regularArbitraryChain model =>
      if wire.answer != false then
        throw "regular CB taxonomy evidence is paired with a true answer"
      let countermodel ← model.decode bounds ontology core superconcept
      have hnot : ¬Entails ontology core superconcept := by
        intro hentails
        rcases countermodel.refutes with
          ⟨D, interpretation, element, hontology, hpositive, hnegative⟩
        exact hnegative (hentails D interpretation hontology element hpositive)
      return {
        coreConcept := core
        core_in_bounds := hcore
        superconcept
        super_in_bounds := hsuper
        answer := false
        exact := ⟨by simp, fun hentails => (hnot hentails).elim⟩
      }
    else throw "taxonomy superconcept escaped its checked bound"
  else throw "taxonomy core concept escaped its checked bound"

structure WireTaxonomy where
  version : Nat
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  ontology : List WireClause
  concept_names : List String
  named_concepts : List Nat
  published : List Bool
  public_subsumptions : List WireSubsumption
  cells : List WireCell
deriving FromJson, ToJson

def WireTaxonomy.bounds (wire : WireTaxonomy) : Bounds :=
  { concepts := wire.concept_count
  , roles := wire.role_count
  , functions := wire.function_count
  , individuals := wire.individual_count }

def coordinates (named : List Nat) : List (Nat × Nat) :=
  named.flatMap fun core => named.map fun superconcept => (core, superconcept)

private def conceptName (names : List String) (id : Nat) : String :=
  names[id]?.getD ""

def publicSubsumptions (names : List String)
    (cells : List (DecodedCell bounds ontology)) : List WireSubsumption :=
  cells.filterMap fun cell =>
    if cell.answer && cell.coreConcept != cell.superconcept then
      some (WireSubsumption.mk (conceptName names cell.coreConcept)
        (conceptName names cell.superconcept))
    else none

structure DecodedTaxonomy where
  bounds : Bounds
  ontology : List FCL
  conceptNames : List String
  concept_name_count : conceptNames.length = bounds.concepts
  concept_names_nodup : conceptNames.Nodup
  named : List Nat
  publicSubsumptions : List WireSubsumption
  public_subsumptions_nodup : publicSubsumptions.Nodup
  cells : List (DecodedCell bounds ontology)
  exact_coordinates : cells.map (fun cell =>
    (cell.coreConcept, cell.superconcept)) = coordinates named
  exact_public : publicSubsumptions.toFinset =
    (CBTaxonomyWire.publicSubsumptions conceptNames cells).toFinset

def WireTaxonomy.decode (wire : WireTaxonomy) : Except String DecodedTaxonomy := do
  if wire.version != 2 then
    throw s!"unsupported CB taxonomy certificate version {wire.version}"
  if wire.concept_count = 0 then
    throw "concept_count must be positive"
  let bounds := wire.bounds
  let ontology ← wire.ontology.mapM (WireClause.decode bounds)
  if hconceptLength : wire.concept_names.length = bounds.concepts then
    if _hconceptNames : wire.concept_names.Nodup then
      if _hnamed : wire.named_concepts.Nodup then
        let named ← wire.named_concepts.mapM
          (checkId "named taxonomy concept" bounds.concepts)
        let cells ← wire.cells.mapM (WireCell.decode bounds ontology)
        if hcoordinates : cells.map (fun cell =>
            (cell.coreConcept, cell.superconcept)) = coordinates named then
          if _hanswers : cells.map (·.answer) = wire.published then
            let expectedPublic := publicSubsumptions wire.concept_names cells
            if _hpublicNodup : wire.public_subsumptions.Nodup then
              if hpublic : wire.public_subsumptions.toFinset = expectedPublic.toFinset then
                return {
                  bounds
                  ontology
                  conceptNames := wire.concept_names
                  concept_name_count := hconceptLength
                  concept_names_nodup := _hconceptNames
                  named
                  publicSubsumptions := wire.public_subsumptions
                  public_subsumptions_nodup := _hpublicNodup
                  cells
                  exact_coordinates := hcoordinates
                  exact_public := hpublic
                }
              else throw "CB public subsumption payload differs from the checked taxonomy"
            else throw "CB public subsumption payload contains duplicates"
          else throw "CB taxonomy publication bits differ from their checked evidence"
        else throw "CB taxonomy cells do not form the complete named-concept matrix"
      else throw "CB taxonomy named concept table contains duplicates"
    else throw "CB concept-name table contains duplicates"
  else throw "CB concept-name table length differs from concept_count"

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
  version := 2
  concept_count := 2
  role_count := 0
  function_count := 0
  individual_count := 0
  ontology := []
  concept_names := ["A", "B"]
  named_concepts := [0, 1]
  published := [true, false, false, true]
  public_subsumptions := []
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
example : rejected ({ exactExample with concept_names := ["A", "A"] }).check = true := by
  native_decide
example : rejected ({ exactExample with public_subsumptions :=
    [{ sub := "A", sup := "B" }] }).check = true := by native_decide

#print axioms DecodedTaxonomy.publishes_exactly
#print axioms WireTaxonomy.check_sound

end ContextCalculus.CBTaxonomyWire
