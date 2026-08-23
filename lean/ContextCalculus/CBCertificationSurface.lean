import ContextCalculus.CBTaxonomyWire

/-!
# Public CB certification surface

This capstone exposes the exact source-bound taxonomy theorem established by
the executable CB certificate checker. It certifies an accepted document, not
an unchecked production run. Rust generation and fail-closed invocation are
separate integration obligations.
-/

namespace ContextCalculus.CB

open ContextCalculus.CBTaxonomyWire

theorem certifiedCBExactTaxonomyPublication
    (wire : WireTaxonomy) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedTaxonomy,
      wire.decode = .ok decoded ∧
        ∀ index : Fin decoded.cells.length,
          decoded.published.get
            ⟨index, by simp [DecodedTaxonomy.published]⟩ = true ↔
          Entails decoded.ontology
            (decoded.cells.get index).coreConcept
            (decoded.cells.get index).superconcept :=
  wire.check_sound hcheck

#print axioms certifiedCBExactTaxonomyPublication

end ContextCalculus.CB
