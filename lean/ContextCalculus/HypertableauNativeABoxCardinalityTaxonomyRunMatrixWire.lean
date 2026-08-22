import ContextCalculus.HypertableauRootedCardinalityTaxonomyProductionRunWire

/-!
# Complete native-ABox cardinality taxonomy run matrices

This wire retains one complete rooted production run for every concept and
ordered subsumption query.  The terminal taxonomy matrix is derived from the
runs inside Lean, so a separately supplied terminal cannot be substituted
after its run has been checked.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireNativeABoxCardinalityTaxonomyRunMatrix where
  version : Nat
  named : List Nat
  concept_runs : List WireRootedCardinalityTaxonomyProductionRun
  subsumption_runs : List (List WireRootedCardinalityTaxonomyProductionRun)
deriving FromJson, ToJson, Repr

def WireNativeABoxCardinalityTaxonomyRunMatrix.shapeB
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix) : Bool :=
  wire.concept_runs.length == wire.named.length &&
  wire.subsumption_runs.length == wire.named.length &&
  wire.subsumption_runs.all fun row => row.length == wire.named.length

def WireNativeABoxCardinalityTaxonomyRunMatrix.allRuns
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix) :
    List WireRootedCardinalityTaxonomyProductionRun :=
  wire.concept_runs ++ wire.subsumption_runs.flatten

def WireNativeABoxCardinalityTaxonomyRunMatrix.runsAcceptedB
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix) : Bool :=
  wire.allRuns.all (WireRootedCardinalityTaxonomyProductionRun.check ·)

def WireNativeABoxCardinalityTaxonomyRunMatrix.terminalMatrix
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix) :
    WireNativeABoxCardinalityTaxonomyMatrix where
  version := wire.version
  named := wire.named
  concepts := wire.concept_runs.map (·.terminal)
  subsumptions := wire.subsumption_runs.map fun row => row.map (·.terminal)

structure DecodedNativeABoxCardinalityTaxonomyRunMatrix where
  wire : WireNativeABoxCardinalityTaxonomyRunMatrix
  terminal : DecodedNativeABoxCardinalityTaxonomyMatrix
  complete_shape : wire.shapeB = true
  runs_accepted : wire.runsAcceptedB = true

def WireNativeABoxCardinalityTaxonomyRunMatrix.decode
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix) :
    Except String DecodedNativeABoxCardinalityTaxonomyRunMatrix := do
  if wire.version != 1 then
    throw s!"unsupported native ABox cardinality taxonomy run matrix version {wire.version}"
  if hshape : wire.shapeB = true then
    if hruns : wire.runsAcceptedB = true then
      let terminal ← wire.terminalMatrix.decode
      return {
        wire
        terminal
        complete_shape := hshape
        runs_accepted := hruns
      }
    else throw "one or more native ABox cardinality taxonomy runs were rejected"
  else throw "native ABox cardinality taxonomy run matrix is incomplete"

def WireNativeABoxCardinalityTaxonomyRunMatrix.check
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix) : Bool :=
  wire.decode.isOk

theorem WireNativeABoxCardinalityTaxonomyRunMatrix.check_sound
    (wire : WireNativeABoxCardinalityTaxonomyRunMatrix)
    (hcheck : wire.check = true) :
    ∃ decoded : DecodedNativeABoxCardinalityTaxonomyRunMatrix,
      wire.decode = .ok decoded ∧ decoded.terminal.SemanticallyValid := by
  unfold WireNativeABoxCardinalityTaxonomyRunMatrix.check at hcheck
  cases hdecode : wire.decode with
  | error message =>
      rw [hdecode] at hcheck
      change false = true at hcheck
      contradiction
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.terminal.semantic_valid⟩

#print axioms WireNativeABoxCardinalityTaxonomyRunMatrix.check_sound

end ContextCalculus.Hypertableau
