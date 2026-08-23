import ContextCalculus.CBJoin3Closure

/-!
# Proof-carrying production CB Join-3 closure

The checker recomputes every residual Join-3 tuple for every context from the
accepted retained snapshot.  Each serialized tuple must be exactly one checked
candidate and name a retained strengthening.  The context sequence itself must
cover the production run exactly once.
-/

namespace ContextCalculus.CBJoin3ClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBHyperClosureWire
open ContextCalculus.CBJoin3Closure
open ContextCalculus.CBFiniteLiteralOrderWire

structure WireJoin3Coverage where
  consumer_index : Nat
  body_index : Nat
  variant_index : Nat
  provider_index : Nat
  provider_head_index : Nat
  bridge_index : Nat
  bridge_head_index : Nat
  conclusion : WireClause
  strengthening_retained : Nat
deriving FromJson, ToJson

def WireJoin3Coverage.signature (wire : WireJoin3Coverage) : Join3Signature := {
  consumerIndex := wire.consumer_index
  bodyIndex := wire.body_index
  variantIndex := wire.variant_index
  providerIndex := wire.provider_index
  providerHeadIndex := wire.provider_head_index
  bridgeIndex := wire.bridge_index
  bridgeHeadIndex := wire.bridge_head_index }

structure DecodedJoin3Coverage
    (order : DecodedFiniteLiteralOrderDocument)
    (context : DecodedProductionContext bounds ontology) where
  signature : Join3Signature
  conclusion : FCL
  candidate_eq : candidateAt? order context.retained signature = some conclusion
  strengtheningIndex : Fin context.retained.length
  strengthens : Strengthens
    (context.retained.get strengtheningIndex) conclusion

def WireJoin3Coverage.decode (order : DecodedFiniteLiteralOrderDocument)
    (context : DecodedProductionContext bounds ontology)
    (wire : WireJoin3Coverage) :
    Except String (DecodedJoin3Coverage order context) := do
  let conclusion ← wire.conclusion.decode bounds
  let signature := wire.signature
  if hcandidate : candidateAt? order context.retained signature = some conclusion then
    if hindex : wire.strengthening_retained < context.retained.length then
      let strengtheningIndex : Fin context.retained.length :=
        ⟨wire.strengthening_retained, hindex⟩
      if hstrengthens : Strengthens
          (context.retained.get strengtheningIndex) conclusion then
        return {
          signature := signature
          conclusion := conclusion
          candidate_eq := hcandidate
          strengtheningIndex := strengtheningIndex
          strengthens := hstrengthens }
      else throw "retained clause does not strengthen Join-3 candidate"
    else throw "Join-3 strengthening index is outside retained clauses"
  else throw "claimed Join-3 tuple is not the checked production candidate"

structure WireContextJoin3Closure where
  context_index : Nat
  context_id : Nat
  generated : List WireJoin3Coverage
deriving FromJson, ToJson

structure DecodedContextJoin3Closure
    (hyper : DecodedHyperClosureDocument) where
  contextIndex : Fin
    hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length
  contextId : Nat
  context_id_eq :
    (hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
      contextIndex).contextId = contextId
  generated : List (DecodedJoin3Coverage hyper.literalOrder
    (hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
      contextIndex))
  candidates_exact : (generated.map fun coverage =>
      (coverage.signature, coverage.conclusion)) =
    candidates hyper.literalOrder
      (hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
        contextIndex).retained

def WireContextJoin3Closure.decode (hyper : DecodedHyperClosureDocument)
    (wire : WireContextJoin3Closure) :
    Except String (DecodedContextJoin3Closure hyper) := do
  let production :=
    hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production
  if hcontext : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length :=
      ⟨wire.context_index, hcontext⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      let generated ← wire.generated.mapM
        (WireJoin3Coverage.decode hyper.literalOrder context)
      let actual := generated.map fun coverage =>
        (coverage.signature, coverage.conclusion)
      let expected := candidates hyper.literalOrder context.retained
      if hexact : actual = expected then
        return {
          contextIndex := contextIndex
          contextId := wire.context_id
          context_id_eq := hid
          generated := generated
          candidates_exact := hexact }
      else throw "Join-3 coverage omits, duplicates, reorders, or invents a candidate"
    else throw "Join-3 context id differs from production context"
  else throw "Join-3 context index is outside the production run"

structure WireJoin3ClosureDocument where
  version : Nat
  hyper_closure : WireHyperClosureDocument
  contexts : List WireContextJoin3Closure
deriving FromJson, ToJson

structure DecodedJoin3ClosureDocument where
  hyper : DecodedHyperClosureDocument
  contexts : List (DecodedContextJoin3Closure hyper)
  context_indices_exact : contexts.map (·.contextIndex.val) =
    List.range
      hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length

def WireJoin3ClosureDocument.decode (wire : WireJoin3ClosureDocument) :
    Except String DecodedJoin3ClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB Join-3-closure version {wire.version}"
  let hyper ← wire.hyper_closure.decode
  let contexts ← wire.contexts.mapM (WireContextJoin3Closure.decode hyper)
  let actual := contexts.map (·.contextIndex.val)
  let expected := List.range
    hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length
  if hexact : actual = expected then
    return { hyper, contexts, context_indices_exact := hexact }
  else throw "Join-3 closure does not cover every context exactly once"

def WireJoin3ClosureDocument.check (wire : WireJoin3ClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedContextJoin3Closure.complete_coverage
    (context : DecodedContextJoin3Closure hyper) :
    ∀ candidate ∈ candidates hyper.literalOrder
        (hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
          context.contextIndex).retained,
      ∃ strengtheningIndex,
        Strengthens
          ((hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
            context.contextIndex).retained.get strengtheningIndex)
          candidate.2 := by
  intro candidate hcandidate
  rw [← context.candidates_exact] at hcandidate
  simp only [List.mem_map] at hcandidate
  obtain ⟨coverage, _hcoverage, heq⟩ := hcandidate
  rw [← heq]
  exact ⟨coverage.strengtheningIndex, coverage.strengthens⟩

theorem WireJoin3ClosureDocument.check_sound
    (wire : WireJoin3ClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedJoin3ClosureDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (·.contextIndex.val) =
        List.range
          decoded.hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.length ∧
      ∀ context ∈ decoded.contexts,
        ∀ candidate ∈ candidates decoded.hyper.literalOrder
            (decoded.hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
              context.contextIndex).retained,
          ∃ strengtheningIndex,
            Strengthens
              ((decoded.hyper.literalOrder.termOrder.factorClosure.localResolution.terminal.sendCoverage.interContext.base.production.contexts.get
                context.contextIndex).retained.get strengtheningIndex)
              candidate.2 := by
  cases hdecode : wire.decode with
  | error message => simp [WireJoin3ClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.context_indices_exact, ?_⟩
      intro context _
      exact context.complete_coverage

#print axioms DecodedContextJoin3Closure.complete_coverage
#print axioms WireJoin3ClosureDocument.check_sound

end ContextCalculus.CBJoin3ClosureWire
