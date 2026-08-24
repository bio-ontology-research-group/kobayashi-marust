import ContextCalculus.CBSourceHyperClosure
import ContextCalculus.CBJoin3Closure

/-!
# Source-bound Join-3 closure

Lean reconstructs every bounded residual Join-3 signature from the terminal
retained clauses and the source-bound literal order. Runtime indexes and
candidate lists are not trusted.
-/

namespace ContextCalculus.CBSourceJoin3Closure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBSourceLocalClosure
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBJoin3Closure

def candidateAt? (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL)
    (signature : Join3Signature) : Option FCL := do
  let consumer ← retained[signature.consumerIndex]?
  let ground ← consumer.body[signature.bodyIndex]?
  let (general, term) ← (variants ground)[signature.variantIndex]?
  let provider ← retained[signature.providerIndex]?
  if signature.providerHeadIndex ∈ order.maximalHeadIndices root provider.head then
    pure ()
  else none
  let providerLiteral ← provider.head[signature.providerHeadIndex]?
  if providerLiteral = general then pure () else none
  let bridge ← retained[signature.bridgeIndex]?
  if signature.providerIndex ≠ signature.bridgeIndex then pure () else none
  if signature.bridgeHeadIndex ∈ order.maximalHeadIndices root bridge.head then
    pure ()
  else none
  let bridgeLiteral ← bridge.head[signature.bridgeHeadIndex]?
  if bridgeLiteral = .eq term (.var 0) then pure () else none
  join3Candidate? consumer provider bridge ground general term

def signatures (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) : List Join3Signature :=
  (List.range retained.length).flatMap fun consumerIndex =>
    match retained[consumerIndex]? with
    | none => []
    | some consumer =>
      (List.range consumer.body.length).flatMap fun bodyIndex =>
        match consumer.body[bodyIndex]? with
        | none => []
        | some ground =>
          (List.range (variants ground).length).flatMap fun variantIndex =>
            (List.range retained.length).flatMap fun providerIndex =>
              match retained[providerIndex]? with
              | none => []
              | some provider =>
                (order.maximalHeadIndices root provider.head).flatMap fun providerHeadIndex =>
                  (List.range retained.length).flatMap fun bridgeIndex =>
                    match retained[bridgeIndex]? with
                    | none => []
                    | some bridge =>
                      (order.maximalHeadIndices root bridge.head).map fun bridgeHeadIndex =>
                        {
                          consumerIndex, bodyIndex, variantIndex, providerIndex,
                          providerHeadIndex, bridgeIndex, bridgeHeadIndex }

def candidates (order : DecodedSourceFiniteOrder production)
    (root : Bool) (retained : List FCL) : List (Join3Signature × FCL) :=
  (signatures order root retained).filterMap fun signature =>
    (candidateAt? order root retained signature).map fun conclusion =>
      (signature, conclusion)

theorem mem_candidates_has_checked_origin
    (order : DecodedSourceFiniteOrder production) (retained : List FCL)
    (root : Bool)
    (candidate : Join3Signature × FCL)
    (hmember : candidate ∈ candidates order root retained) :
    candidateAt? order root retained candidate.1 = some candidate.2 := by
  simp only [candidates, List.mem_filterMap] at hmember
  obtain ⟨signature, _hsignature, hcandidate⟩ := hmember
  cases hresult : candidateAt? order root retained signature with
  | none => simp [hresult] at hcandidate
  | some conclusion =>
      simp only [hresult, Option.map_some, Option.some.injEq,
        Prod.mk.injEq] at hcandidate
      rcases hcandidate with ⟨rfl, rfl⟩
      exact hresult

def sourceJoin3ClosedB (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology) : Bool :=
  (candidates order context.root context.retained).all fun candidate =>
    hasStrengthening context.retained candidate.2

theorem sourceJoin3ClosedB_sound
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology)
    (hclosed : sourceJoin3ClosedB order context = true) :
    ∀ candidate ∈ candidates order context.root context.retained,
      ∃ clause ∈ context.retained, Strengthens clause candidate.2 := by
  intro candidate hcandidate
  have h := List.all_eq_true.mp hclosed candidate hcandidate
  exact (hasStrengthening_eq_true_iff context.retained candidate.2).mp h

structure WireSourceJoin3ClosureDocument where
  version : Nat
  hyper_closure : WireSourceHyperClosureDocument
deriving FromJson, ToJson

structure DecodedSourceJoin3ClosureDocument where
  hyperClosure : DecodedSourceHyperClosureDocument
  join3_closed : ∀ context ∈
      hyperClosure.localClosure.live.production.contexts,
    sourceJoin3ClosedB hyperClosure.order context = true

def WireSourceJoin3ClosureDocument.decode
    (wire : WireSourceJoin3ClosureDocument) :
    Except String DecodedSourceJoin3ClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB Join-3-closure version {wire.version}"
  let hyperClosure ← wire.hyper_closure.decode
  if hclosed : ∀ context ∈
      hyperClosure.localClosure.live.production.contexts,
      sourceJoin3ClosedB hyperClosure.order context = true then
    return { hyperClosure, join3_closed := hclosed }
  else throw "source-bound CB terminal state is not Join-3-closed"

def WireSourceJoin3ClosureDocument.check
    (wire : WireSourceJoin3ClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedSourceJoin3ClosureDocument.complete_coverage
    (decoded : DecodedSourceJoin3ClosureDocument) :
    ∀ context ∈ decoded.hyperClosure.localClosure.live.production.contexts,
      ∀ candidate ∈ candidates decoded.hyperClosure.order context.root context.retained,
        ∃ clause ∈ context.retained, Strengthens clause candidate.2 := by
  intro context hcontext
  exact sourceJoin3ClosedB_sound decoded.hyperClosure.order context
    (decoded.join3_closed context hcontext)

theorem WireSourceJoin3ClosureDocument.check_sound
    (wire : WireSourceJoin3ClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceJoin3ClosureDocument,
      wire.decode = .ok decoded ∧
      ∀ context ∈ decoded.hyperClosure.localClosure.live.production.contexts,
        ∀ candidate ∈ candidates decoded.hyperClosure.order context.root context.retained,
          ∃ clause ∈ context.retained, Strengthens clause candidate.2 := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceJoin3ClosureDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.complete_coverage⟩

#print axioms mem_candidates_has_checked_origin
#print axioms sourceJoin3ClosedB_sound
#print axioms WireSourceJoin3ClosureDocument.check_sound

end ContextCalculus.CBSourceJoin3Closure
