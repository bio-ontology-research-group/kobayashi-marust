import ContextCalculus.HypertableauCardinalityTaxonomyProductionRunWire

/-!
# Complete ontology-only cardinality taxonomy run matrices

Every terminal cell of the semantic taxonomy is derived from its retained
production run. Shape, shared problem data, query coordinates, every run, and
the resulting complete taxonomy are checked in one artifact.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireCardinalityTaxonomyRunMatrix where
  version : Nat
  named : List Nat
  concept_runs : List WireCardinalityTaxonomyProductionRun
  subsumption_runs : List (List WireCardinalityTaxonomyProductionRun)
deriving FromJson, ToJson, Repr

def WireCardinalityTaxonomyRunMatrix.shapeB
    (wire : WireCardinalityTaxonomyRunMatrix) : Bool :=
  wire.concept_runs.length == wire.named.length &&
    wire.subsumption_runs.length == wire.named.length &&
    wire.subsumption_runs.all fun row => row.length == wire.named.length

def WireCardinalityTaxonomyRunMatrix.coordinatesB
    (wire : WireCardinalityTaxonomyRunMatrix) : Bool :=
  (wire.concept_runs.zip wire.named).all fun (run, concept) =>
      toJson run.query == toJson (WireCardinalityTaxonomyQuery.concept concept) &&
  (wire.subsumption_runs.zip wire.named).all fun (row, sub) =>
      (row.zip wire.named).all fun (run, sup) =>
        toJson run.query == toJson (WireCardinalityTaxonomyQuery.subsumption sub sup)

def WireCardinalityTaxonomyRunMatrix.allRuns
    (wire : WireCardinalityTaxonomyRunMatrix) :
    List WireCardinalityTaxonomyProductionRun :=
  wire.concept_runs ++ wire.subsumption_runs.flatten

def WireCardinalityTaxonomyRunMatrix.runsAcceptedB
    (wire : WireCardinalityTaxonomyRunMatrix) : Bool :=
  wire.allRuns.all (WireCardinalityTaxonomyProductionRun.check ·)

def WireCardinalityTaxonomyRunMatrix.sameProblemB
    (wire : WireCardinalityTaxonomyRunMatrix) : Bool :=
  match wire.allRuns with
  | [] => false
  | first :: rest => rest.all fun run =>
      run.concept_count == first.concept_count &&
      run.role_count == first.role_count &&
      run.variable_count == first.variable_count &&
      toJson run.ontology == toJson first.ontology &&
      toJson run.definitions == toJson first.definitions

def WireCardinalityTaxonomyRunMatrix.terminalMatrix?
    (wire : WireCardinalityTaxonomyRunMatrix) :
    Option WireCardinalityTaxonomyCertificate :=
  match wire.allRuns with
  | [] => none
  | first :: _ => some {
      version := 5
      concept_count := first.concept_count
      role_count := first.role_count
      variable_count := first.variable_count
      ontology := first.ontology
      definitions := first.definitions
      named := wire.named
      concepts := wire.concept_runs.map (·.terminal)
      subsumptions := wire.subsumption_runs.map fun row => row.map (·.terminal)
    }

structure DecodedCardinalityTaxonomyRunMatrix where
  wire : WireCardinalityTaxonomyRunMatrix
  terminal : DecodedCardinalityTaxonomyCertificate
  complete_shape : wire.shapeB = true
  coordinates : wire.coordinatesB = true
  same_problem : wire.sameProblemB = true
  runs_accepted : wire.runsAcceptedB = true

def WireCardinalityTaxonomyRunMatrix.decode
    (wire : WireCardinalityTaxonomyRunMatrix) :
    Except String DecodedCardinalityTaxonomyRunMatrix := do
  if wire.version != 1 then
    throw s!"unsupported cardinality taxonomy run matrix version {wire.version}"
  if hshape : wire.shapeB = true then
    if hcoordinates : wire.coordinatesB = true then
      if hproblem : wire.sameProblemB = true then
        if hruns : wire.runsAcceptedB = true then
          match wire.terminalMatrix? with
          | none => throw "cardinality taxonomy run matrix has no cells"
          | some terminal =>
              let decoded ← terminal.decode
              return ⟨wire, decoded, hshape, hcoordinates, hproblem, hruns⟩
        else throw "one or more cardinality taxonomy runs were rejected"
      else throw "cardinality taxonomy runs do not share one problem"
    else throw "cardinality taxonomy run coordinates do not match their cells"
  else throw "cardinality taxonomy run matrix is incomplete"

def WireCardinalityTaxonomyRunMatrix.check
    (wire : WireCardinalityTaxonomyRunMatrix) : Bool := wire.decode.isOk

theorem WireCardinalityTaxonomyRunMatrix.check_sound
    (wire : WireCardinalityTaxonomyRunMatrix) (hcheck : wire.check = true) :
    ∃ decoded : DecodedCardinalityTaxonomyRunMatrix,
      wire.decode = .ok decoded ∧
        ∃ certificate : CompleteCardinalityTaxonomyCertificate
          decoded.terminal.ontology decoded.terminal.definitions
          decoded.terminal.named,
          certificate = decoded.terminal.semantic := by
  unfold WireCardinalityTaxonomyRunMatrix.check at hcheck
  cases hdecode : wire.decode with
  | error message =>
      rw [hdecode] at hcheck
      change false = true at hcheck
      contradiction
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.terminal.check_sound⟩

#print axioms WireCardinalityTaxonomyRunMatrix.check_sound

end ContextCalculus.Hypertableau
