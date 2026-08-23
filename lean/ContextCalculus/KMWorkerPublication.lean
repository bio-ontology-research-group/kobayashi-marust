import ContextCalculus.ELCompletionExecutablePublication
import ContextCalculus.HypertableauExecutablePublicationWire
import ContextCalculus.CBCertificationSurface

/-!
# Unified executable worker-publication boundary

The automatic supervisor may receive an answer from ELC, HT, or CB.  This
module gives those independently certified wire formats one tagged checker and
one soundness theorem.  The tag chooses a decoder only; it contributes no
semantic premise.  Every branch must rerun the corresponding source-bound
worker checker and recover that worker's complete publication contract.

The next routing layer still has to prove that the decoded worker source is a
semantics-preserving translation of the exact source supplied to the router.
That obligation is deliberately not represented by this tag.
-/

namespace ContextCalculus.KMWorkerPublication

open ContextCalculus

inductive WirePublication where
  | elc (document : ELCompletion.WireCertificate)
  | htGlobal (document : Hypertableau.WireExecutableHTGlobalPublication)
  | htTaxonomy (document : Hypertableau.WireExecutableHTTaxonomyPublication)
  | cbTaxonomy
      (document : CBLiveExactTaxonomyPublication.WireLiveExactTaxonomyPublication)
deriving Lean.FromJson, Lean.ToJson

/-- One fail-closed entry point for all production worker documents. -/
def WirePublication.check : WirePublication → Except String Bool
  | .elc document => document.check
  | .htGlobal document => .ok document.check
  | .htTaxonomy document => .ok document.check
  | .cbTaxonomy document => document.check

/-- Branch-specific semantic payload recovered after acceptance.  Each case
retains its decoded source and exact publication theorem rather than erasing it
to an untrusted Boolean. -/
def WirePublication.SemanticallyValid : WirePublication → Prop
  | .elc document =>
      ∃ decoded : ELCompletion.DecodedCertificate document.symbol_count,
        document.decode = .ok decoded ∧
          ELCompletion.PublicationSemantics decoded
  | .htGlobal document => document.SemanticallyValid
  | .htTaxonomy document => document.SemanticallyValid
  | .cbTaxonomy document =>
      ∃ decoded : CBLiveExactTaxonomyPublication.DecodedLiveExactTaxonomyPublication,
        document.decode = .ok decoded ∧
        decoded.named.toFinset =
          (CBLiveExactTaxonomyPublication.liveNamedConcepts decoded.live).toFinset ∧
        decoded.cells.map (fun cell => (cell.sub, cell.sup)) =
          CBLiveExactTaxonomyPublication.coordinates decoded.named ∧
        ∀ index : Fin decoded.cells.length,
          (decoded.cells.get index).answer = true ↔
            CBLiveExactTaxonomyPublication.SourceExactEntails decoded.live
              ⟨(decoded.cells.get index).sub,
                (decoded.cells.get index).sub_in_bounds⟩
              ⟨(decoded.cells.get index).sup,
                (decoded.cells.get index).sup_in_bounds⟩

/-- Acceptance by the unified worker checker establishes the full existing
source-bound capstone for the selected worker. -/
theorem WirePublication.check_sound (wire : WirePublication)
    (hcheck : wire.check = .ok true) : wire.SemanticallyValid := by
  cases wire with
  | elc document =>
      exact document.check_publication_semantics hcheck
  | htGlobal document =>
      exact document.check_sound (by simpa [WirePublication.check] using hcheck)
  | htTaxonomy document =>
      exact document.check_sound (by simpa [WirePublication.check] using hcheck)
  | cbTaxonomy document =>
      exact CB.certifiedCBProductionExactTaxonomyPublication document hcheck

#print axioms WirePublication.check_sound

end ContextCalculus.KMWorkerPublication
