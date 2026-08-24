import ContextCalculus.CBSourceTaxonomyWire
import ContextCalculus.CBLiveExactTaxonomyPublication
import ContextCalculus.CBStandaloneContextProofWire
import ContextCalculus.CBSourceProductionTaxonomyWire
import ContextCalculus.CBGlobalProductionClosure

/-!
# Public CB certification surface

This capstone exposes the exact typed-source-bound taxonomy theorem established
by the executable CB certificate checker. It certifies an accepted document,
not an unchecked production run. Rust generation and fail-closed invocation
are separate integration obligations.
-/

namespace ContextCalculus.CB

open ContextCalculus.CBTaxonomyWire
open ContextCalculus.CBSourceTaxonomyWire
open ContextCalculus.CBLiveExactTaxonomyPublication
open ContextCalculus.CBStandaloneContextProofWire
open ContextCalculus.CBGlobalClosureWire
open ContextCalculus.CBGlobalProductionClosure

/-- An accepted global-closure document covers every production context for
local Resolution, Factor, Eq, Hyper, Join-3, Succ, and r-Succ. All branches are
bound to the same source, retained context snapshots, and finite orders by the
global decoder. -/
theorem certifiedCBGlobalProductionClosure
    (wire : WireCBGlobalClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCBGlobalClosureDocument,
      wire.decode = .ok decoded ∧ GlobalProductionClosed decoded := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireCBGlobalClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl,
        CBGlobalProductionClosure.DecodedCBGlobalClosureDocument.production_closed
          decoded⟩

#print axioms certifiedCBGlobalProductionClosure

/-- The compact native CB publication capstone: one typed source, one shared
chronological production DAG, and one complete positive-or-countermodel matrix
are accepted together and publish exactly the source semantics. -/
theorem certifiedCBSharedProductionTaxonomyPublication
    (wire : CBSourceProductionTaxonomyWire.WireDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : CBSourceProductionTaxonomyWire.DecodedDocument,
      wire.decode = .ok decoded ∧
      ∀ index : Fin decoded.cells.length,
        (decoded.cells.map (·.answer)).get ⟨index, by simp⟩ = true ↔
          decoded.SourceEntails (decoded.cells.get index) :=
  wire.check_sound hcheck

#print axioms certifiedCBSharedProductionTaxonomyPublication

/-- Every node accepted by the chronological source-bound proof checker is
context-valid in every model of the exact typed ontology. This includes local
production and arbitrarily nested cross-context Pred derivations. -/
theorem certifiedCBStandaloneContextProof
    (bounds : CBTermWire.Bounds) (ontology : List CheckerTerm.FCL)
    (wire : WireStandaloneProof)
    (hcheck : wire.check bounds ontology = .ok true) :
    ∃ decoded : DecodedStandaloneProof ontology,
      wire.decode bounds ontology = .ok decoded ∧
      ∀ node ∈ decoded.nodes, ∀ {D : Type} (model : CheckerTerm.TModel D),
        (∀ source ∈ ontology, CheckerTerm.valid model source) →
        CBInterContext.ContextValid model node.core node.clause := by
  cases hdecode : wire.decode bounds ontology with
  | error message =>
      simp [WireStandaloneProof.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      intro node hnode D model hontology
      exact node.contextValid model hontology

#print axioms certifiedCBStandaloneContextProof

theorem certifiedCBExactTaxonomyPublication
    (wire : WireTaxonomy) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedTaxonomy,
      wire.decode = .ok decoded ∧
        decoded.publicSubsumptions.toFinset =
          (publicSubsumptions decoded.conceptNames decoded.cells).toFinset ∧
        ∀ index : Fin decoded.cells.length,
          decoded.published.get
            ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
          Entails decoded.ontology
            (decoded.cells.get index).coreConcept
            (decoded.cells.get index).superconcept := by
  rcases wire.check_sound hcheck with ⟨decoded, hdecode, hexact⟩
  exact ⟨decoded, hdecode, decoded.exact_public, hexact⟩

#print axioms certifiedCBExactTaxonomyPublication

/-- An accepted joint document publishes exactly the complete taxonomy of its
typed normalized source ontology. The checker requires exact identity of the
source encoding, symbol bounds, taxonomy clause list, matrix, and public
payload. -/
theorem certifiedCBSourceExactTaxonomyPublication
    (wire : WireSourceTaxonomy) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceTaxonomy,
      wire.decode = .ok decoded ∧
        decoded.taxonomy.publicSubsumptions.toFinset =
          (publicSubsumptions decoded.taxonomy.conceptNames
            decoded.taxonomy.cells).toFinset ∧
        ∀ index : Fin decoded.taxonomy.cells.length,
          decoded.taxonomy.published.get
            ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
          decoded.SourceEntails (decoded.taxonomy.cells.get index) := by
  rcases wire.check_sound hcheck with ⟨decoded, hdecode, hexact⟩
  exact ⟨decoded, hdecode, decoded.taxonomy.exact_public, hexact⟩

#print axioms certifiedCBSourceExactTaxonomyPublication

/-- The production-bound capstone: an accepted live document enumerates every
materialized named-concept coordinate and publishes exactly the typed source
semantics at that coordinate. Positive cells are tied to checked chronological
production derivations; negative cells carry independently checked finite,
blocked, or regular countermodels. -/
theorem certifiedCBProductionExactTaxonomyPublication
    (wire : WireLiveExactTaxonomyPublication)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLiveExactTaxonomyPublication,
      wire.decode = .ok decoded ∧
      decoded.named.toFinset = (liveNamedConcepts decoded.live).toFinset ∧
      decoded.cells.map (fun cell => (cell.sub, cell.sup)) =
        CBLiveExactTaxonomyPublication.coordinates decoded.named ∧
      ∀ index : Fin decoded.cells.length,
        (decoded.cells.get index).answer = true ↔
          SourceExactEntails decoded.live
            ⟨(decoded.cells.get index).sub,
              (decoded.cells.get index).sub_in_bounds⟩
            ⟨(decoded.cells.get index).sup,
              (decoded.cells.get index).sup_in_bounds⟩ := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireLiveExactTaxonomyPublication.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.named_exact, decoded.coordinates_exact,
        decoded.cell_source_exact⟩

#print axioms certifiedCBProductionExactTaxonomyPublication

end ContextCalculus.CB
