import ContextCalculus.HypertableauOrdinaryTaxonomyProductionRunWire

/-!
# Complete ontology-only ordinary taxonomy run matrices

The semantic taxonomy is derived from one retained production run per concept
and ordered subsumption query. No independently supplied terminal matrix is
trusted.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireOrdinaryTaxonomyRunMatrix where
  version : Nat
  named : List Nat
  concept_runs : List WireOrdinaryTaxonomyProductionRun
  subsumption_runs : List (List WireOrdinaryTaxonomyProductionRun)
deriving FromJson, ToJson, Repr

def WireOrdinaryTaxonomyRunMatrix.shapeB
    (wire : WireOrdinaryTaxonomyRunMatrix) : Bool :=
  wire.concept_runs.length == wire.named.length &&
    wire.subsumption_runs.length == wire.named.length &&
    wire.subsumption_runs.all fun row => row.length == wire.named.length

def WireOrdinaryTaxonomyRunMatrix.coordinatesB
    (wire : WireOrdinaryTaxonomyRunMatrix) : Bool :=
  (wire.concept_runs.zip wire.named).all fun (run, concept) =>
      toJson run.query == toJson (WireOrdinaryTaxonomyQuery.concept concept) &&
  (wire.subsumption_runs.zip wire.named).all fun (row, sub) =>
      (row.zip wire.named).all fun (run, sup) =>
        toJson run.query == toJson (WireOrdinaryTaxonomyQuery.subsumption sub sup)

def WireOrdinaryTaxonomyRunMatrix.allRuns
    (wire : WireOrdinaryTaxonomyRunMatrix) :
    List WireOrdinaryTaxonomyProductionRun :=
  wire.concept_runs ++ wire.subsumption_runs.flatten

def WireOrdinaryTaxonomyRunMatrix.runsAcceptedB
    (wire : WireOrdinaryTaxonomyRunMatrix) : Bool :=
  wire.allRuns.all (WireOrdinaryTaxonomyProductionRun.check ·)

def WireOrdinaryTaxonomyRunMatrix.sameProblemB
    (wire : WireOrdinaryTaxonomyRunMatrix) : Bool :=
  match wire.allRuns with
  | [] => false
  | first :: rest => rest.all fun run =>
      run.concept_count == first.concept_count &&
      run.role_count == first.role_count &&
      run.variable_count == first.variable_count &&
      toJson run.ontology == toJson first.ontology

def WireOrdinaryTaxonomyRunMatrix.terminalMatrix?
    (wire : WireOrdinaryTaxonomyRunMatrix) : Option WireMixedTaxonomyCertificate :=
  match wire.allRuns with
  | [] => none
  | first :: _ => some {
      version := 2
      concept_count := first.concept_count
      role_count := first.role_count
      variable_count := first.variable_count
      ontology := first.ontology
      named := wire.named
      concepts := wire.concept_runs.map (·.terminal)
      subsumptions := wire.subsumption_runs.map fun row => row.map (·.terminal)
    }

structure DecodedOrdinaryTaxonomyRunMatrix where
  wire : WireOrdinaryTaxonomyRunMatrix
  terminal : DecodedMixedTaxonomyCertificate
  complete_shape : wire.shapeB = true
  coordinates : wire.coordinatesB = true
  same_problem : wire.sameProblemB = true
  runs_accepted : wire.runsAcceptedB = true

def WireOrdinaryTaxonomyRunMatrix.decode
    (wire : WireOrdinaryTaxonomyRunMatrix) :
    Except String DecodedOrdinaryTaxonomyRunMatrix := do
  if wire.version != 1 then
    throw s!"unsupported ordinary taxonomy run matrix version {wire.version}"
  if hshape : wire.shapeB = true then
    if hcoordinates : wire.coordinatesB = true then
      if hproblem : wire.sameProblemB = true then
        if hruns : wire.runsAcceptedB = true then
          match wire.terminalMatrix? with
          | none => throw "ordinary taxonomy run matrix has no cells"
          | some terminal =>
              let decoded ← terminal.decode
              return ⟨wire, decoded, hshape, hcoordinates, hproblem, hruns⟩
        else throw "one or more ordinary taxonomy runs were rejected"
      else throw "ordinary taxonomy runs do not share one problem"
    else throw "ordinary taxonomy run coordinates do not match their cells"
  else throw "ordinary taxonomy run matrix is incomplete"

def WireOrdinaryTaxonomyRunMatrix.check
    (wire : WireOrdinaryTaxonomyRunMatrix) : Bool := wire.decode.isOk

theorem WireOrdinaryTaxonomyRunMatrix.check_sound
    (wire : WireOrdinaryTaxonomyRunMatrix) (hcheck : wire.check = true) :
    ∃ decoded : DecodedOrdinaryTaxonomyRunMatrix,
      wire.decode = .ok decoded ∧
        Nonempty (CompleteTaxonomyCertificate decoded.terminal.ontology
          decoded.terminal.named) := by
  unfold WireOrdinaryTaxonomyRunMatrix.check at hcheck
  cases hdecode : wire.decode with
  | error message =>
      rw [hdecode] at hcheck
      change false = true at hcheck
      contradiction
  | ok decoded => exact ⟨decoded, rfl, ⟨decoded.terminal.semantic⟩⟩

#print axioms WireOrdinaryTaxonomyRunMatrix.check_sound

end ContextCalculus.Hypertableau
