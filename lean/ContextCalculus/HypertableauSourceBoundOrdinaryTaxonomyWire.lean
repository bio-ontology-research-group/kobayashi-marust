import ContextCalculus.HypertableauNormalizedTaxonomyWire
import ContextCalculus.HypertableauOrdinaryTaxonomyRunMatrixWire

/-!
# Source-bound ordinary production taxonomy

This is the publication boundary for an ontology-only ordinary HT taxonomy.
The normalized source certificate and the complete production-run matrix are
not accepted independently: the target taxonomy carried by the normalization
wrapper must be exactly the matrix derived from the retained production runs.
-/

namespace ContextCalculus.Hypertableau

open Lean

structure WireSourceBoundOrdinaryTaxonomy where
  version : Nat
  source : WireNormalizedTaxonomyCertificate
  runs : WireOrdinaryTaxonomyRunMatrix
deriving FromJson, ToJson, Repr

def WireSourceBoundOrdinaryTaxonomy.payloadBoundB
    (wire : WireSourceBoundOrdinaryTaxonomy) : Bool :=
  match wire.source.payload, wire.runs.terminalMatrix? with
  | .mixed sourceTarget, some runTarget =>
      toJson sourceTarget == toJson runTarget
  | _, _ => false

def WireSourceBoundOrdinaryTaxonomy.check
    (wire : WireSourceBoundOrdinaryTaxonomy) : Bool :=
  wire.version == 1 && wire.source.check && wire.runs.check && wire.payloadBoundB

theorem WireSourceBoundOrdinaryTaxonomy.check_sound
    (wire : WireSourceBoundOrdinaryTaxonomy) (hcheck : wire.check = true) :
    wire.source.check = true ∧ wire.runs.check = true ∧
      wire.payloadBoundB = true ∧
      ∃ decoded : DecodedNormalizedTaxonomyCertificate,
        wire.source.decode = .ok decoded ∧ decoded.SemanticallyComplete := by
  have parts : wire.version = 1 ∧ wire.source.check = true ∧
      wire.runs.check = true ∧ wire.payloadBoundB = true := by
    have nested : ((wire.version = 1 ∧ wire.source.check = true) ∧
        wire.runs.check = true) ∧ wire.payloadBoundB = true := by
      simpa [WireSourceBoundOrdinaryTaxonomy.check, Bool.and_eq_true,
        beq_iff_eq] using hcheck
    exact ⟨nested.1.1.1, nested.1.1.2, nested.1.2, nested.2⟩
  refine ⟨parts.2.1, parts.2.2.1, parts.2.2.2, ?_⟩
  have hsource := parts.2.1
  cases hdecode : wire.source.decode with
  | error message =>
      unfold WireNormalizedTaxonomyCertificate.check at hsource
      rw [hdecode] at hsource
      change false = true at hsource
      contradiction
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      cases decoded with
      | plain decoded => exact ⟨decoded.semantic, rfl⟩
      | mixed decoded => exact ⟨decoded.semantic, rfl⟩

#print axioms WireSourceBoundOrdinaryTaxonomy.check_sound

end ContextCalculus.Hypertableau
