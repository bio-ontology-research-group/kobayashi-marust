import ContextCalculus.HypertableauRootedOrdinaryTaxonomyProductionRunWire
import ContextCalculus.HypertableauNativeABoxTaxonomyMatrixWire

/-!
# Complete native-ABox taxonomy run matrices

The checker retains one complete rooted ordinary run for every concept and
ordered subsumption query. Lean derives the terminal matrix from these runs,
so terminal evidence cannot be detached from the search that produced it.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireNativeABoxTaxonomyRunMatrix where
  version : Nat
  named : List Nat
  concept_runs : List WireRootedOrdinaryTaxonomyProductionRun
  subsumption_runs : List (List WireRootedOrdinaryTaxonomyProductionRun)
deriving FromJson, ToJson, Repr

def WireNativeABoxTaxonomyRunMatrix.shapeB
    (wire : WireNativeABoxTaxonomyRunMatrix) : Bool :=
  wire.concept_runs.length == wire.named.length &&
  wire.subsumption_runs.length == wire.named.length &&
  wire.subsumption_runs.all fun row => row.length == wire.named.length

def WireNativeABoxTaxonomyRunMatrix.allRuns
    (wire : WireNativeABoxTaxonomyRunMatrix) :
    List WireRootedOrdinaryTaxonomyProductionRun :=
  wire.concept_runs ++ wire.subsumption_runs.flatten

def WireNativeABoxTaxonomyRunMatrix.runsAcceptedB
    (wire : WireNativeABoxTaxonomyRunMatrix) : Bool :=
  wire.allRuns.all (WireRootedOrdinaryTaxonomyProductionRun.check ·)

def WireNativeABoxTaxonomyRunMatrix.terminalMatrix
    (wire : WireNativeABoxTaxonomyRunMatrix) : WireNativeABoxTaxonomyMatrix where
  version := wire.version
  named := wire.named
  concepts := wire.concept_runs.map (·.terminal)
  subsumptions := wire.subsumption_runs.map fun row => row.map (·.terminal)

structure DecodedNativeABoxTaxonomyRunMatrix where
  wire : WireNativeABoxTaxonomyRunMatrix
  terminal : DecodedNativeABoxTaxonomyMatrix
  complete_shape : wire.shapeB = true
  runs_accepted : wire.runsAcceptedB = true

def WireNativeABoxTaxonomyRunMatrix.decode
    (wire : WireNativeABoxTaxonomyRunMatrix) :
    Except String DecodedNativeABoxTaxonomyRunMatrix := do
  if wire.version != 1 then
    throw s!"unsupported native ABox taxonomy run matrix version {wire.version}"
  if hshape : wire.shapeB = true then
    if hruns : wire.runsAcceptedB = true then
      let terminal ← wire.terminalMatrix.decode
      return { wire, terminal, complete_shape := hshape, runs_accepted := hruns }
    else throw "one or more native ABox taxonomy runs were rejected"
  else throw "native ABox taxonomy run matrix is incomplete"

def WireNativeABoxTaxonomyRunMatrix.check
    (wire : WireNativeABoxTaxonomyRunMatrix) : Bool :=
  wire.decode.isOk

theorem WireNativeABoxTaxonomyRunMatrix.check_sound
    (wire : WireNativeABoxTaxonomyRunMatrix) (hcheck : wire.check = true) :
    ∃ decoded : DecodedNativeABoxTaxonomyRunMatrix,
      wire.decode = .ok decoded ∧ decoded.terminal.SemanticallyValid := by
  unfold WireNativeABoxTaxonomyRunMatrix.check at hcheck
  cases hdecode : wire.decode with
  | error message =>
      rw [hdecode] at hcheck
      change false = true at hcheck
      contradiction
  | ok decoded => exact ⟨decoded, rfl, decoded.terminal.semantic_valid⟩

#print axioms WireNativeABoxTaxonomyRunMatrix.check_sound

end ContextCalculus.Hypertableau
