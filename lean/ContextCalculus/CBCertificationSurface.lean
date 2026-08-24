import ContextCalculus.CBSourceTaxonomyWire
import ContextCalculus.CBLiveExactTaxonomyPublication
import ContextCalculus.CBLiveInsertionDerivation
import ContextCalculus.CBSourceLiveInsertionDerivation
import ContextCalculus.CBSourceLocalClosure
import ContextCalculus.CBSourceHyperClosure
import ContextCalculus.CBSourceJoin3Closure
import ContextCalculus.CBSourceSuccClosure
import ContextCalculus.CBSourceEqClosure
import ContextCalculus.CBSourceOrdinaryPredClosure
import ContextCalculus.CBStandaloneContextProofWire
import ContextCalculus.CBSourceProductionTaxonomyWire
import ContextCalculus.CBGlobalProductionClosure
import ContextCalculus.CBGlobalModelWire

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
open ContextCalculus.CBLiveInsertionDerivation
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceLocalClosure
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceJoin3Closure
open ContextCalculus.CBSourceSuccClosure
open ContextCalculus.CBSourceEqClosure
open ContextCalculus.CBSourceOrdinaryPredClosure
open ContextCalculus.CBLiveStateWire
open ContextCalculus.CBInterContext
open ContextCalculus.CBInterContextWire
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

/-- The model-existence half of CB completeness over the finite blocked
grounding. One accepted document proves every production rule family closed
and, when its complete blocked saturation omits bottom, constructs a nonempty
model of the exact production clause list, including checked Skolem allocation.
-/
theorem certifiedCBClashFreeGlobalProductionModel
    (wire : CBGlobalModelWire.WireCBGlobalModelDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : CBGlobalModelWire.DecodedCBGlobalModelDocument,
      wire.decode = .ok decoded ∧
      GlobalProductionClosed decoded.global ∧
      (PropRes.PClause.bot ∉ decoded.blocked.certificate.terminal →
        ∃ (D : Type) (model : CheckerTerm.TModel D), Nonempty D ∧
          ∀ clause ∈
              (CBGlobalClosureWire.rProduction decoded.global.rsucc).source.ontology,
            CheckerTerm.valid model clause) := by
  cases hdecode : wire.decode with
  | error message =>
      simp [CBGlobalModelWire.WireCBGlobalModelDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl,
        CBGlobalProductionClosure.DecodedCBGlobalClosureDocument.production_closed
          decoded.global,
        decoded.production_model⟩

#print axioms certifiedCBClashFreeGlobalProductionModel

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

/-- The production execution bridge. An accepted live insertion document
proves every final retained clause context-valid and consequently proves every
terminal Pred transfer and arrival sound. No imported clause remains an
untrusted local-trace premise. -/
theorem certifiedCBLiveProductionDerivation
    (wire : WireLiveInsertionDerivationDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLiveInsertionDerivationDocument,
      wire.decode = .ok decoded ∧
      ∀ (D : Type) (model : CheckerTerm.TModel D),
        (∀ source ∈
          (rProduction decoded.live.global.global.rsucc).source.ontology,
          CheckerTerm.valid model source) →
        ProductionRetainedValid
          (rProduction decoded.live.global.global.rsucc) model ∧
        (∀ transfer ∈
            (terminalOfGlobal decoded.live.global).sendCoverage.interContext.base.transfers,
          CheckerTerm.valid model transfer.payload) ∧
        (∀ arrival ∈
            (terminalOfGlobal decoded.live.global).sendCoverage.interContext.arrivals,
          ContextValid model
            ((terminalOfGlobal decoded.live.global).sendCoverage.interContext.base.production.contexts.get
              arrival.receiverIndex).core arrival.result) := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireLiveInsertionDerivationDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      intro D model hontology
      refine ⟨decoded.production_retained_valid model hontology, ?_, ?_⟩
      · intro transfer _
        exact decoded.terminal_pred_transfer_valid model hontology transfer
      · intro arrival _
        exact decoded.terminal_pred_arrival_valid model hontology arrival

#print axioms certifiedCBLiveProductionDerivation

/-- Native soundness boundary independent of a preassembled global
completeness certificate. The exact typed source, terminal context snapshot,
and chronological insertion evidence suffice to prove every retained clause
context-valid. -/
theorem certifiedCBSourceLiveProductionDerivation
    (wire : WireSourceLiveInsertionDerivationDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceLiveInsertionDerivationDocument,
      wire.decode = .ok decoded ∧
      ∀ (D : Type) (model : CheckerTerm.TModel D),
        (∀ source ∈ decoded.production.source.ontology,
          CheckerTerm.valid model source) →
        ProductionRetainedValid decoded.production model :=
  wire.check_sound hcheck

#print axioms certifiedCBSourceLiveProductionDerivation

/-- Native local-fixpoint boundary. Lean recomputes every terminal local
Resolution and Factor candidate and checks a retained strengthening, rather
than trusting a candidate list emitted by Rust. -/
theorem certifiedCBSourceLocalClosure
    (wire : WireSourceLocalClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceLocalClosureDocument,
      wire.decode = .ok decoded ∧
      (∀ context ∈ decoded.live.production.contexts,
        ∀ candidate ∈ localResolutionCandidates context.retained,
          ∃ clause ∈ context.retained,
            CBProductionTrace.Strengthens clause candidate) ∧
      (∀ context ∈ decoded.live.production.contexts,
        (∀ clause ∈ context.retained,
          CBLocalFactorClosureWire.terminalHeadNormal clause.head = true) ∧
        (∀ candidate ∈
            CBLocalFactorClosureWire.factorCandidates context.retained,
          ∃ clause ∈ context.retained,
            CBProductionTrace.Strengthens clause candidate.2)) :=
  wire.check_sound hcheck

#print axioms certifiedCBSourceLocalClosure

/-- Source-bound Hyper fixpoint boundary. Lean reconstructs the exact finite
term and literal universe, enumerates every source substitution and maximal
provider selection, and checks retained strengthening of each conclusion. -/
theorem certifiedCBSourceHyperClosure
    (wire : WireSourceHyperClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceHyperClosureDocument,
      wire.decode = .ok decoded ∧
      ∀ context ∈ decoded.localClosure.live.production.contexts,
        ∀ candidate ∈ CBSourceHyperClosure.hyperCandidates decoded.order
            context.root context.retained
            decoded.localClosure.live.production.source.ontology,
          ∃ clause ∈ context.retained,
            CBProductionTrace.Strengthens clause candidate :=
  wire.check_sound hcheck

#print axioms certifiedCBSourceHyperClosure

/-- Source-bound residual Join-3 fixpoint boundary. Lean enumerates every
bounded consumer/provider/equality-bridge tuple and requires retained
strengthening of every checked conclusion. -/
theorem certifiedCBSourceJoin3Closure
    (wire : WireSourceJoin3ClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceJoin3ClosureDocument,
      wire.decode = .ok decoded ∧
      ∀ context ∈
          decoded.hyperClosure.localClosure.live.production.contexts,
        ∀ candidate ∈ CBSourceJoin3Closure.candidates
            decoded.hyperClosure.order context.root context.retained,
          ∃ clause ∈ context.retained,
            CBProductionTrace.Strengthens clause candidate.2 :=
  wire.check_sound hcheck

#print axioms certifiedCBSourceJoin3Closure

/-- Source-bound residual Succ fixpoint boundary. Lean independently
reconstructs direct Succ and r-Succ offers from retained clauses and live edges,
then requires delivery and retained target strengthening for every offer. -/
theorem certifiedCBSourceSuccClosure
    (wire : WireSourceSuccClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceSuccClosureDocument,
      wire.decode = .ok decoded := by
  obtain ⟨decoded, hdecode, _, _⟩ := wire.check_sound hcheck
  exact ⟨decoded, hdecode⟩

#print axioms certifiedCBSourceSuccClosure

/-- Source-bound ordered-paramodulation fixpoint boundary. The decoded witness
contains independently reconstructed closure over every terminal context. -/
theorem certifiedCBSourceEqClosure
    (wire : WireSourceEqClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceEqClosureDocument,
      wire.decode = .ok decoded := by
  obtain ⟨decoded, hdecode, _⟩ := wire.check_sound hcheck
  exact ⟨decoded, hdecode⟩

#print axioms certifiedCBSourceEqClosure

/-- Source-bound ordinary Pred send and arrival fixpoint boundary. Nominal-ground
r-Pred remains a separate certification family. -/
theorem certifiedCBSourceOrdinaryPredClosure
    (wire : WireSourceOrdinaryPredClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceOrdinaryPredClosureDocument,
      wire.decode = .ok decoded := by
  obtain ⟨decoded, hdecode, _⟩ := wire.check_sound hcheck
  exact ⟨decoded, hdecode⟩

#print axioms certifiedCBSourceOrdinaryPredClosure

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
