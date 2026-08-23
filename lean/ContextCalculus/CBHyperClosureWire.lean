import ContextCalculus.CBHyperClosure

/-!
# Proof-carrying production CB Hyper closure

This wire layer recomputes the complete finite Hyper candidate list for every
production context.  The certificate must list that exact sequence and point
to a retained clause that strengthens each candidate.  It therefore cannot
omit a source substitution, provider product, or context, and it cannot trust
the engine's transient indexes or queue state.
-/

namespace ContextCalculus.CBHyperClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBHyperClosure

structure WireHyperCoverage where
  conclusion : WireClause
  strengthening_retained : Nat
deriving FromJson, ToJson

structure DecodedHyperCoverage
    (context : DecodedProductionContext bounds ontology) where
  conclusion : FCL
  strengtheningIndex : Fin context.retained.length
  strengthens : Strengthens
    (context.retained.get strengtheningIndex) conclusion

def WireHyperCoverage.decode
    (context : DecodedProductionContext bounds ontology)
    (wire : WireHyperCoverage) : Except String (DecodedHyperCoverage context) := do
  let conclusion ← wire.conclusion.decode bounds
  if hindex : wire.strengthening_retained < context.retained.length then
    let strengtheningIndex : Fin context.retained.length :=
      ⟨wire.strengthening_retained, hindex⟩
    if hstrengthens : Strengthens
        (context.retained.get strengtheningIndex) conclusion then
      return { conclusion, strengtheningIndex, strengthens := hstrengthens }
    else throw "retained clause does not strengthen Hyper candidate"
  else throw "Hyper strengthening index is outside retained clauses"

structure WireContextHyperClosure where
  context_index : Nat
  context_id : Nat
  generated : List WireHyperCoverage
deriving FromJson, ToJson

structure DecodedContextHyperClosure
    (literalOrder : DecodedFiniteLiteralOrderDocument) where
  contextIndex : Fin
    literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length
  contextId : Nat
  context_id_eq :
    (literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
      contextIndex).contextId = contextId
  generated : List (DecodedHyperCoverage
    (literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
      contextIndex))
  candidates_exact : generated.map (·.conclusion) =
    hyperCandidates literalOrder literalOrder.termOrder.orderedTerms
      (literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
        contextIndex).retained
      literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.source.ontology

def WireContextHyperClosure.decode
    (literalOrder : DecodedFiniteLiteralOrderDocument)
    (wire : WireContextHyperClosure) :
    Except String (DecodedContextHyperClosure literalOrder) := do
  let production :=
    literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production
  if hcontext : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length :=
      ⟨wire.context_index, hcontext⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      let generated ← wire.generated.mapM (WireHyperCoverage.decode context)
      let actual := generated.map (·.conclusion)
      let expected := hyperCandidates literalOrder
        literalOrder.termOrder.orderedTerms context.retained
        production.source.ontology
      if hexact : actual = expected then
        return {
          contextIndex
          contextId := wire.context_id
          context_id_eq := hid
          generated
          candidates_exact := hexact }
      else throw "Hyper coverage omits, duplicates, reorders, or invents a candidate"
    else throw "Hyper context id differs from production context"
  else throw "Hyper context index is outside the production run"

structure WireHyperClosureDocument where
  version : Nat
  literal_order : WireFiniteLiteralOrderDocument
  contexts : List WireContextHyperClosure
deriving FromJson, ToJson

structure DecodedHyperClosureDocument where
  literalOrder : DecodedFiniteLiteralOrderDocument
  contexts : List (DecodedContextHyperClosure literalOrder)
  context_indices_exact : contexts.map (·.contextIndex.val) =
    List.range
      literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length

def WireHyperClosureDocument.decode (wire : WireHyperClosureDocument) :
    Except String DecodedHyperClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB Hyper-closure version {wire.version}"
  let literalOrder ← wire.literal_order.decode
  let contexts ← wire.contexts.mapM
    (WireContextHyperClosure.decode literalOrder)
  let actual := contexts.map (·.contextIndex.val)
  let expected := List.range
    literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length
  if hexact : actual = expected then
    return { literalOrder, contexts, context_indices_exact := hexact }
  else throw "Hyper closure does not cover every context exactly once"

def WireHyperClosureDocument.check (wire : WireHyperClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedContextHyperClosure.complete_coverage
    (context : DecodedContextHyperClosure literalOrder) :
    ∀ candidate ∈ hyperCandidates literalOrder
        literalOrder.termOrder.orderedTerms
        (literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
          context.contextIndex).retained
        literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.source.ontology,
      ∃ strengtheningIndex,
        Strengthens
          ((literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
            context.contextIndex).retained.get strengtheningIndex)
          candidate := by
  intro candidate hcandidate
  rw [← context.candidates_exact] at hcandidate
  simp only [List.mem_map] at hcandidate
  obtain ⟨coverage, _hcoverage, rfl⟩ := hcandidate
  exact ⟨coverage.strengtheningIndex, coverage.strengthens⟩

theorem WireHyperClosureDocument.check_sound
    (wire : WireHyperClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedHyperClosureDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (·.contextIndex.val) =
        List.range
          decoded.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length ∧
      ∀ context ∈ decoded.contexts,
        ∀ candidate ∈ hyperCandidates decoded.literalOrder
            decoded.literalOrder.termOrder.orderedTerms
            (decoded.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained
            decoded.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.source.ontology,
          ∃ strengtheningIndex,
            Strengthens
              ((decoded.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
                context.contextIndex).retained.get strengtheningIndex)
              candidate := by
  cases hdecode : wire.decode with
  | error message => simp [WireHyperClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.context_indices_exact, ?_⟩
      intro context _
      exact context.complete_coverage

#print axioms DecodedContextHyperClosure.complete_coverage
#print axioms WireHyperClosureDocument.check_sound

end ContextCalculus.CBHyperClosureWire
