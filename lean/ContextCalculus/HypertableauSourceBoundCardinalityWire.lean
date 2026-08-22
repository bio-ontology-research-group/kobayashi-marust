import ContextCalculus.HypertableauNormalizedWire
import ContextCalculus.HypertableauCardinalityProductionRunWire
import ContextCalculus.HypertableauCardinalityTaxonomyRunMatrixWire
import ContextCalculus.HypertableauCardinalityTaxonomyWire

/-!
# Source-bound ontology-only cardinality production evidence

Global and complete-taxonomy publication documents bind checked source
normalization to the exact terminal or terminal matrix reconstructed from the
retained cardinality production runs.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireSourceBoundCardinalityGlobal where
  version : Nat
  source : WireNormalizedCertificate
  run : WireCardinalityProductionRun
deriving FromJson, ToJson, Repr

def WireSourceBoundCardinalityGlobal.payloadBoundB
    (wire : WireSourceBoundCardinalityGlobal) : Bool :=
  match wire.source.payload with
  | .cardinality certificate => toJson certificate == toJson wire.run.terminal
  | _ => false

def WireSourceBoundCardinalityGlobal.sourceAcceptedB
    (wire : WireSourceBoundCardinalityGlobal) : Bool :=
  match wire.source.check with
  | .ok true => true
  | _ => false

def WireSourceBoundCardinalityGlobal.check
    (wire : WireSourceBoundCardinalityGlobal) : Bool :=
  wire.version == 1 && wire.sourceAcceptedB && wire.run.check && wire.payloadBoundB

theorem WireSourceBoundCardinalityGlobal.check_sound
    (wire : WireSourceBoundCardinalityGlobal) (hcheck : wire.check = true) :
    wire.source.check = .ok true ∧ wire.run.check = true ∧
      wire.payloadBoundB = true ∧
      ∃ decoded : DecodedNormalizedCertificate,
        wire.source.decode = .ok decoded ∧ decoded.SemanticallyValid := by
  have nested : (((wire.version = 1 ∧ wire.sourceAcceptedB = true) ∧
      wire.run.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundCardinalityGlobal.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  have hsource : wire.source.check = .ok true := by
    unfold WireSourceBoundCardinalityGlobal.sourceAcceptedB at nested
    cases h : wire.source.check with
    | error message => simp [h] at nested
    | ok accepted => cases accepted <;> simp [h] at nested ⊢
  refine ⟨hsource, nested.1.2, nested.2, ?_⟩
  unfold WireNormalizedCertificate.check at hsource
  cases hdecode : wire.source.decode with
  | error message => simp [hdecode] at hsource
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.check_sound ?_⟩
      simpa [WireNormalizedCertificate.check, hdecode] using hsource

structure WireSourceBoundCardinalityTaxonomy where
  version : Nat
  source : WireNormalizedCardinalityTaxonomyCertificate
  runs : WireCardinalityTaxonomyRunMatrix
deriving FromJson, ToJson, Repr

def WireSourceBoundCardinalityTaxonomy.payloadBoundB
    (wire : WireSourceBoundCardinalityTaxonomy) : Bool :=
  match wire.runs.terminalMatrix? with
  | some terminal => toJson wire.source.certificate == toJson terminal
  | none => false

def WireSourceBoundCardinalityTaxonomy.check
    (wire : WireSourceBoundCardinalityTaxonomy) : Bool :=
  wire.version == 1 && wire.source.check && wire.runs.check && wire.payloadBoundB

theorem WireSourceBoundCardinalityTaxonomy.check_sound
    (wire : WireSourceBoundCardinalityTaxonomy) (hcheck : wire.check = true) :
    wire.source.check = true ∧ wire.runs.check = true ∧
      wire.payloadBoundB = true ∧
      ∃ decoded : DecodedNormalizedCardinalityTaxonomyCertificate,
        wire.source.decode = .ok decoded ∧
        ∃ certificate : CompleteCardinalityTaxonomyCertificate
          decoded.normalization.source decoded.target.definitions decoded.target.named,
          certificate = decoded.semantic := by
  have nested : (((wire.version = 1 ∧ wire.source.check = true) ∧
      wire.runs.check = true) ∧ wire.payloadBoundB = true) := by
    simpa [WireSourceBoundCardinalityTaxonomy.check, Bool.and_eq_true,
      beq_iff_eq] using hcheck
  refine ⟨nested.1.1.2, nested.1.2, nested.2, ?_⟩
  have hsource := nested.1.1.2
  unfold WireNormalizedCardinalityTaxonomyCertificate.check at hsource
  cases hdecode : wire.source.decode with
  | error message =>
      rw [hdecode] at hsource
      contradiction
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.check_sound⟩

#print axioms WireSourceBoundCardinalityGlobal.check_sound
#print axioms WireSourceBoundCardinalityTaxonomy.check_sound

end ContextCalculus.Hypertableau
