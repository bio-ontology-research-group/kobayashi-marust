import ContextCalculus.CBFiniteModel
import ContextCalculus.CBTermDerivationWire
import Lean

/-!
# Bounds-checked CB finite-countermodel wire

The wire carries complete finite truth and function tables.  Decoding checks
every table dimension and every domain-valued entry against the symbol bounds
of the source CB document.  Acceptance proves that the exact decoded source
ontology has a model containing a witness for a failed subsumption.
-/

namespace ContextCalculus.CBFiniteModelWire

open Lean ContextCalculus CheckerTerm CBFiniteModel
open ContextCalculus.CBTermWire

structure WireFiniteModel where
  domain_size : Nat
  concepts : List (List Bool)
  roles : List (List (List Bool))
  constants : List Nat
  functions : List (List Nat)
deriving FromJson, ToJson, Repr

structure DecodedFiniteModel (bounds : Bounds) where
  domainSize : Nat
  domain_nonempty : 0 < domainSize
  concepts : List (List Bool)
  roles : List (List (List Bool))
  constants : List (Fin domainSize)
  functions : List (List (Fin domainSize))
  concept_count : concepts.length = bounds.concepts
  concept_width : ∀ row ∈ concepts, row.length = domainSize
  role_count : roles.length = bounds.roles
  role_width : ∀ table ∈ roles,
    table.length = domainSize ∧ ∀ row ∈ table, row.length = domainSize
  constant_count : constants.length = bounds.individuals
  function_count : functions.length = bounds.functions
  function_width : ∀ row ∈ functions, row.length = domainSize

private def getBool (rows : List (List Bool)) (index element : Nat) : Bool :=
  (rows[index]?.getD []).getD element false

private def getRole (tables : List (List (List Bool)))
    (index source target : Nat) : Bool :=
  ((tables[index]?.getD [])[source]?.getD []).getD target false

def DecodedFiniteModel.model (decoded : DecodedFiniteModel bounds) :
    FiniteTModel decoded.domainSize where
  domain_nonempty := decoded.domain_nonempty
  concept concept element := getBool decoded.concepts concept element
  role role source target := getRole decoded.roles role source target
  constant individual := decoded.constants.getD individual
    ⟨0, decoded.domain_nonempty⟩
  function function argument := (decoded.functions[function]?.getD []).getD
    argument ⟨0, decoded.domain_nonempty⟩

private def decodeDomainValue (domainSize value : Nat) :
    Except String (Fin domainSize) :=
  if h : value < domainSize then return ⟨value, h⟩
  else throw s!"finite-model value {value} is outside [0,{domainSize})"

def WireFiniteModel.decode (bounds : Bounds) (wire : WireFiniteModel) :
    Except String (DecodedFiniteModel bounds) := do
  if hdomain : 0 < wire.domain_size then
    if hconceptCount : wire.concepts.length = bounds.concepts then
      if hconceptWidth : ∀ row ∈ wire.concepts,
          row.length = wire.domain_size then
        if hroleCount : wire.roles.length = bounds.roles then
          if hroleWidth : ∀ table ∈ wire.roles,
              table.length = wire.domain_size ∧
                ∀ row ∈ table, row.length = wire.domain_size then
            let constants ← wire.constants.mapM
              (decodeDomainValue wire.domain_size)
            let functions ← wire.functions.mapM fun row =>
              row.mapM (decodeDomainValue wire.domain_size)
            if hconstantCount : constants.length = bounds.individuals then
              if hfunctionCount : functions.length = bounds.functions then
                if hfunctionWidth : ∀ row ∈ functions,
                    row.length = wire.domain_size then
                  return {
                    domainSize := wire.domain_size
                    domain_nonempty := hdomain
                    concepts := wire.concepts
                    roles := wire.roles
                    constants
                    functions
                    concept_count := hconceptCount
                    concept_width := hconceptWidth
                    role_count := hroleCount
                    role_width := hroleWidth
                    constant_count := hconstantCount
                    function_count := hfunctionCount
                    function_width := hfunctionWidth
                  }
                else throw "finite-model function table has the wrong width"
              else throw "finite-model function table count differs from function_count"
            else throw "finite-model constant table count differs from individual_count"
          else throw "finite-model role table has the wrong dimensions"
        else throw "finite-model role table count differs from role_count"
      else throw "finite-model concept table has the wrong width"
    else throw "finite-model concept table count differs from concept_count"
  else throw "finite-model domain must be nonempty"

structure WireCountermodel where
  core_concept : Nat
  superconcept : Nat
  witness : Nat
  model : WireFiniteModel
deriving FromJson, ToJson, Repr

structure DecodedCountermodel (bounds : Bounds) (ontology : List FCL) where
  coreConcept : Nat
  superconcept : Nat
  modelWire : WireFiniteModel
  finite : DecodedFiniteModel bounds
  witness : Fin finite.domainSize
  models_source : finite.model.modelsB ontology = true
  has_core : finite.model.concept coreConcept witness = true
  omits_super : finite.model.concept superconcept witness = false

def WireCountermodel.decode (bounds : Bounds) (ontology : List FCL)
    (wire : WireCountermodel) :
    Except String (DecodedCountermodel bounds ontology) := do
  let core ← checkId "countermodel core concept" bounds.concepts wire.core_concept
  let superconcept ← checkId "countermodel superconcept" bounds.concepts wire.superconcept
  let finite ← wire.model.decode bounds
  let witness ← decodeDomainValue finite.domainSize wire.witness
  if hmodels : finite.model.modelsB ontology = true then
    if hcore : finite.model.concept core witness = true then
      if hsuper : finite.model.concept superconcept witness = false then
        return {
          coreConcept := core
          superconcept
          modelWire := wire.model
          finite
          witness
          models_source := hmodels
          has_core := hcore
          omits_super := hsuper
        }
      else throw "finite countermodel satisfies the claimed superclass at its witness"
    else throw "finite countermodel does not satisfy the core concept at its witness"
  else throw "finite countermodel does not model the complete source ontology"

def WireCountermodel.check (bounds : Bounds) (ontology : List FCL)
    (wire : WireCountermodel) : Except String Bool := do
  let _ ← wire.decode bounds ontology
  return true

def DecodedCountermodel.Refutes
    (decoded : DecodedCountermodel bounds ontology) : Prop :=
    ¬∀ (D : Type) (model : TModel D),
      (∀ clause ∈ ontology, valid model clause) →
      ∀ element, model.conc decoded.coreConcept element →
        model.conc decoded.superconcept element

theorem DecodedCountermodel.refutes_subsumption
    (decoded : DecodedCountermodel bounds ontology) : decoded.Refutes := by
  intro hentails
  have hsource := decoded.finite.model.modelsB_sound ontology decoded.models_source
  have hconclusion := hentails (Fin decoded.finite.domainSize)
    decoded.finite.model.toModel hsource decoded.witness decoded.has_core
  simp only [FiniteTModel.toModel] at hconclusion
  rw [decoded.omits_super] at hconclusion
  contradiction

theorem WireCountermodel.check_sound (bounds : Bounds) (ontology : List FCL)
    (wire : WireCountermodel) (hcheck : wire.check bounds ontology = .ok true) :
    ∃ decoded : DecodedCountermodel bounds ontology,
      wire.decode bounds ontology = .ok decoded ∧ decoded.Refutes := by
  cases hdecode : wire.decode bounds ontology with
  | error message => simp [WireCountermodel.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.refutes_subsumption⟩

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

private def exampleBounds : Bounds :=
  { concepts := 2, roles := 0, functions := 0, individuals := 0 }

private def exampleOntology : List FCL :=
  [⟨[.P (.concept 0 (.var 0))], [.P (.concept 0 (.var 0))]⟩]

private def exampleCountermodel : WireCountermodel where
  core_concept := 0
  superconcept := 1
  witness := 0
  model := {
    domain_size := 1
    concepts := [[true], [false]]
    roles := []
    constants := []
    functions := []
  }

example : exampleCountermodel.check exampleBounds exampleOntology = .ok true := by
  native_decide

example : rejected (({ exampleCountermodel with witness := 1 }).check
    exampleBounds exampleOntology) = true := by native_decide

example : rejected (({ exampleCountermodel with model :=
    { exampleCountermodel.model with concepts := [[true], [true]] } }).check
    exampleBounds exampleOntology) = true := by native_decide

#print axioms DecodedCountermodel.refutes_subsumption
#print axioms WireCountermodel.check_sound

end ContextCalculus.CBFiniteModelWire
