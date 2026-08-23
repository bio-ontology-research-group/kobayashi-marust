import ContextCalculus.CBRSuccClosure

/-!
# Proof-carrying production r-Succ closure

The route must explicitly assert that r-Succ was enabled and provide KM's
reach-concept id table.  The checker validates that table's finite shape, then
recomputes every context's complete edge/reach cross-product.  Each product
entry must already occur on the checked predecessor edge and its target must
retain the corresponding tautological hypothesis.
-/

namespace ContextCalculus.CBRSuccClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBPredSendCoverageWire
open ContextCalculus.CBJoin3ClosureWire ContextCalculus.CBSuccClosure
open ContextCalculus.CBSuccClosureWire ContextCalculus.CBRSuccClosure
open ContextCalculus.CBInterContext

def productionOf (succ : DecodedSuccClosureDocument) :=
  ContextCalculus.CBSuccClosureWire.productionOf succ.join3

def sendCoverageOf (succ : DecodedSuccClosureDocument) :=
  (ContextCalculus.CBSuccClosureWire.terminalOf succ.join3).sendCoverage

structure WireRSuccCoverage where
  edge : WireTerm
  target_context_index : Nat
  source_predicate : WirePredicate
  pushed : WirePredicate
  strengthening_retained : Nat
deriving FromJson, ToJson

structure DecodedRSuccCoverage (succ : DecodedSuccClosureDocument)
    (sourceIndex : Fin (productionOf succ).contexts.length) where
  offer : RSuccOffer
  targetIndex : Fin (productionOf succ).contexts.length
  target_eq : offer.edge.targetIndex = targetIndex.val
  edge_delivered : edgeDelivered succ.join3 sourceIndex.val targetIndex.val
    { edge := offer.edge.label, pushed := offer.pushed } = true
  strengtheningIndex : Fin
    ((productionOf succ).contexts.get targetIndex).retained.length
  strengthens : Strengthens
    (((productionOf succ).contexts.get targetIndex).retained.get strengtheningIndex)
    (succHypothesis offer.pushed)

def WireRSuccCoverage.decode (succ : DecodedSuccClosureDocument)
    (sourceIndex : Fin (productionOf succ).contexts.length)
    (wire : WireRSuccCoverage) :
    Except String (DecodedRSuccCoverage succ sourceIndex) := do
  let edgeLabel ← wire.edge.decode (productionOf succ).bounds
  let sourcePredicate ← wire.source_predicate.decode (productionOf succ).bounds
  let pushed ← wire.pushed.decode (productionOf succ).bounds
  if htarget : wire.target_context_index < (productionOf succ).contexts.length then
    let targetIndex : Fin (productionOf succ).contexts.length :=
      ⟨wire.target_context_index, htarget⟩
    let edge : OutgoingEdge := { label := edgeLabel, targetIndex := targetIndex.val }
    let offer : RSuccOffer := { edge, sourcePredicate, pushed }
    if hdelivery : edgeDelivered succ.join3 sourceIndex.val targetIndex.val
        { edge := edgeLabel, pushed := pushed } = true then
      let target := (productionOf succ).contexts.get targetIndex
      if hstrengthening : wire.strengthening_retained < target.retained.length then
        let strengtheningIndex : Fin target.retained.length :=
          ⟨wire.strengthening_retained, hstrengthening⟩
        if hstrengthens : Strengthens (target.retained.get strengtheningIndex)
            (succHypothesis pushed) then
          return {
            offer := offer
            targetIndex := targetIndex
            target_eq := rfl
            edge_delivered := hdelivery
            strengtheningIndex := strengtheningIndex
            strengthens := hstrengthens
          }
        else throw "target retained clause does not strengthen r-Succ hypothesis"
      else throw "r-Succ strengthening index is outside target retained clauses"
    else throw "r-Succ payload is absent from the checked predecessor edge"
  else throw "r-Succ target index is outside the production run"

structure WireContextRSuccClosure where
  source_context_index : Nat
  source_context_id : Nat
  offers : List WireRSuccCoverage
deriving FromJson, ToJson

structure DecodedContextRSuccClosure (succ : DecodedSuccClosureDocument)
    (reachConcepts : List Nat) where
  sourceIndex : Fin (productionOf succ).contexts.length
  sourceId : Nat
  source_id_eq : ((productionOf succ).contexts.get sourceIndex).contextId = sourceId
  offers : List (DecodedRSuccCoverage succ sourceIndex)
  offers_exact : offers.map (·.offer) =
    rSuccOffers (sendCoverageOf succ) reachConcepts succ.join3.hyper.literalOrder
      sourceIndex.val ((productionOf succ).contexts.get sourceIndex).retained

def WireContextRSuccClosure.decode (succ : DecodedSuccClosureDocument)
    (reachConcepts : List Nat) (wire : WireContextRSuccClosure) :
    Except String (DecodedContextRSuccClosure succ reachConcepts) := do
  if hsource : wire.source_context_index < (productionOf succ).contexts.length then
    let sourceIndex : Fin (productionOf succ).contexts.length :=
      ⟨wire.source_context_index, hsource⟩
    let source := (productionOf succ).contexts.get sourceIndex
    if hid : source.contextId = wire.source_context_id then
      let offers ← wire.offers.mapM (WireRSuccCoverage.decode succ sourceIndex)
      let expected := rSuccOffers (sendCoverageOf succ) reachConcepts
        succ.join3.hyper.literalOrder sourceIndex.val source.retained
      if hexact : offers.map (·.offer) = expected then
        return {
          sourceIndex := sourceIndex
          sourceId := wire.source_context_id
          source_id_eq := hid
          offers := offers
          offers_exact := hexact
        }
      else throw "r-Succ coverage differs from the complete edge/reach cross-product"
    else throw "r-Succ source id differs from production context"
  else throw "r-Succ source index is outside the production run"

structure WireRSuccClosureDocument where
  version : Nat
  rsucc_enabled : Bool
  succ_closure : WireSuccClosureDocument
  reach_concepts : List Nat
  contexts : List WireContextRSuccClosure
deriving FromJson, ToJson

structure DecodedRSuccClosureDocument where
  succ : DecodedSuccClosureDocument
  reachConcepts : List Nat
  reach_nodup : reachConcepts.Nodup
  reach_bounded : ∀ concept ∈ reachConcepts,
    concept < (productionOf succ).bounds.concepts
  contexts : List (DecodedContextRSuccClosure succ reachConcepts)
  context_indices_exact : contexts.map (·.sourceIndex.val) =
    List.range (productionOf succ).contexts.length

def WireRSuccClosureDocument.decode (wire : WireRSuccClosureDocument) :
    Except String DecodedRSuccClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB r-Succ-closure version {wire.version}"
  if wire.rsucc_enabled != true then
    throw "certified r-Succ closure requires KM_RSUCC enabled"
  let succ ← wire.succ_closure.decode
  if hnodup : wire.reach_concepts.Nodup then
    if hbounded : ∀ concept ∈ wire.reach_concepts,
        concept < (productionOf succ).bounds.concepts then
      let contexts ← wire.contexts.mapM
        (WireContextRSuccClosure.decode succ wire.reach_concepts)
      if hexact : contexts.map (·.sourceIndex.val) =
          List.range (productionOf succ).contexts.length then
        return {
          succ := succ
          reachConcepts := wire.reach_concepts
          reach_nodup := hnodup
          reach_bounded := hbounded
          contexts := contexts
          context_indices_exact := hexact
        }
      else throw "r-Succ closure does not cover every source context exactly once"
    else throw "r-Succ reach-concept id is outside the production signature"
  else throw "r-Succ reach-concept table contains duplicates"

def WireRSuccClosureDocument.check (wire : WireRSuccClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedContextRSuccClosure.complete_delivery
    (context : DecodedContextRSuccClosure succ reachConcepts) :
    ∀ offer ∈ rSuccOffers (sendCoverageOf succ) reachConcepts
        succ.join3.hyper.literalOrder context.sourceIndex.val
        ((productionOf succ).contexts.get context.sourceIndex).retained,
      ∃ targetIndex strengtheningIndex,
        offer.edge.targetIndex = targetIndex.val ∧
        edgeDelivered succ.join3 context.sourceIndex.val targetIndex.val
          { edge := offer.edge.label, pushed := offer.pushed } = true ∧
        Strengthens
          (((productionOf succ).contexts.get targetIndex).retained.get
            strengtheningIndex) (succHypothesis offer.pushed) := by
  intro offer hoffer
  rw [← context.offers_exact] at hoffer
  simp only [List.mem_map] at hoffer
  obtain ⟨coverage, _, rfl⟩ := hoffer
  exact ⟨coverage.targetIndex, coverage.strengtheningIndex,
    coverage.target_eq, coverage.edge_delivered, coverage.strengthens⟩

#print axioms DecodedContextRSuccClosure.complete_delivery

end ContextCalculus.CBRSuccClosureWire
