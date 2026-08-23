import ContextCalculus.CBSuccClosure

/-!
# Proof-carrying direct Succ delivery

Every direct offer is recomputed from a sender's retained clauses.  Its target
must contain a retained strengthening of the tautological hypothesis and the
same `(predecessor, edge, pushed)` triple must occur in the already checked Pred
return-edge snapshot.  This makes Succ and Pred certify one shared edge rather
than two unrelated serialized claims.
-/

namespace ContextCalculus.CBSuccClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBPredSendCoverageWire
open ContextCalculus.CBJoin3ClosureWire
open ContextCalculus.CBSuccClosure
open ContextCalculus.CBInterContext

def terminalOf (join3 : DecodedJoin3ClosureDocument) :=
  join3.hyper.literalOrder.termOrder.factorClosure.localResolution.terminal

def productionOf (join3 : DecodedJoin3ClosureDocument) :=
  (terminalOf join3).sendCoverage.interContext.base.production

/-- The exact reverse edge already accepted by Pred coverage. -/
def edgeDelivered (join3 : DecodedJoin3ClosureDocument)
    (senderIndex targetIndex : Nat) (offer : Offer) : Bool :=
  let sendCoverage := (terminalOf join3).sendCoverage
  match offer.edge with
  | .app _ _ =>
      match sendCoverage.senders.find? fun snapshot =>
          snapshot.senderIndex.val = targetIndex with
      | none => false
      | some snapshot => snapshot.edges.any fun edge =>
          edge.receiverIndex.val = senderIndex && edge.label = offer.edge &&
            decide (offer.pushed ∈ edge.pushed)
  | .const individual =>
      match sendCoverage.rootSender with
      | none => false
      | some snapshot => snapshot.senderIndex.val = targetIndex &&
          snapshot.edges.any fun edge =>
            edge.receiverIndex.val = senderIndex && edge.individual = individual &&
              decide (offer.pushed ∈ edge.pushed)
  | _ => false

structure WireSuccCoverage where
  edge : WireTerm
  pushed : WirePredicate
  target_context_index : Nat
  target_context_id : Nat
  strengthening_retained : Nat
deriving FromJson, ToJson

structure DecodedSuccCoverage (join3 : DecodedJoin3ClosureDocument)
    (senderIndex : Fin (productionOf join3).contexts.length) where
  offer : Offer
  targetIndex : Fin (productionOf join3).contexts.length
  targetId : Nat
  target_id_eq :
    ((productionOf join3).contexts.get targetIndex).contextId = targetId
  edge_delivered : edgeDelivered join3 senderIndex.val targetIndex.val offer = true
  strengtheningIndex : Fin
    ((productionOf join3).contexts.get targetIndex).retained.length
  strengthens : Strengthens
    (((productionOf join3).contexts.get targetIndex).retained.get strengtheningIndex)
    (succHypothesis offer.pushed)

def WireSuccCoverage.decode (join3 : DecodedJoin3ClosureDocument)
    (senderIndex : Fin (productionOf join3).contexts.length)
    (wire : WireSuccCoverage) :
    Except String (DecodedSuccCoverage join3 senderIndex) := do
  let edge ← wire.edge.decode (productionOf join3).bounds
  let pushed ← wire.pushed.decode (productionOf join3).bounds
  let offer : Offer := { edge, pushed }
  if htarget : wire.target_context_index < (productionOf join3).contexts.length then
    let targetIndex : Fin (productionOf join3).contexts.length :=
      ⟨wire.target_context_index, htarget⟩
    let target := (productionOf join3).contexts.get targetIndex
    if hid : target.contextId = wire.target_context_id then
      if hdelivery : edgeDelivered join3 senderIndex.val targetIndex.val offer = true then
        if hstrengthening : wire.strengthening_retained < target.retained.length then
          let strengtheningIndex : Fin target.retained.length :=
            ⟨wire.strengthening_retained, hstrengthening⟩
          if hstrengthens : Strengthens
              (target.retained.get strengtheningIndex)
              (succHypothesis offer.pushed) then
            return {
              offer
              targetIndex
              targetId := wire.target_context_id
              target_id_eq := hid
              edge_delivered := hdelivery
              strengtheningIndex
              strengthens := hstrengthens }
          else throw "target retained clause does not strengthen Succ hypothesis"
        else throw "Succ hypothesis strengthening index is outside target retained clauses"
      else throw "Succ offer is absent from the target's checked predecessor edge"
    else throw "Succ target id differs from production context"
  else throw "Succ target index is outside the production run"

structure WireContextSuccClosure where
  sender_context_index : Nat
  sender_context_id : Nat
  offers : List WireSuccCoverage
deriving FromJson, ToJson

structure DecodedContextSuccClosure (join3 : DecodedJoin3ClosureDocument) where
  senderIndex : Fin (productionOf join3).contexts.length
  senderId : Nat
  sender_id_eq : ((productionOf join3).contexts.get senderIndex).contextId = senderId
  offers : List (DecodedSuccCoverage join3 senderIndex)
  offers_exact : offers.map (·.offer) =
    directOffers join3.hyper.literalOrder
      ((productionOf join3).contexts.get senderIndex).retained

def WireContextSuccClosure.decode (join3 : DecodedJoin3ClosureDocument)
    (wire : WireContextSuccClosure) :
    Except String (DecodedContextSuccClosure join3) := do
  if hsender : wire.sender_context_index < (productionOf join3).contexts.length then
    let senderIndex : Fin (productionOf join3).contexts.length :=
      ⟨wire.sender_context_index, hsender⟩
    let sender := (productionOf join3).contexts.get senderIndex
    if hid : sender.contextId = wire.sender_context_id then
      let offers ← wire.offers.mapM (WireSuccCoverage.decode join3 senderIndex)
      let actual := offers.map (·.offer)
      let expected := directOffers join3.hyper.literalOrder sender.retained
      if hexact : actual = expected then
        return {
          senderIndex := senderIndex
          senderId := wire.sender_context_id
          sender_id_eq := hid
          offers := offers
          offers_exact := hexact
        }
      else throw "direct Succ coverage omits, duplicates, reorders, or invents an offer"
    else throw "Succ sender id differs from production context"
  else throw "Succ sender index is outside the production run"

structure WireSuccClosureDocument where
  version : Nat
  join3_closure : WireJoin3ClosureDocument
  contexts : List WireContextSuccClosure
deriving FromJson, ToJson

structure DecodedSuccClosureDocument where
  join3 : DecodedJoin3ClosureDocument
  contexts : List (DecodedContextSuccClosure join3)
  context_indices_exact : contexts.map (·.senderIndex.val) =
    List.range (productionOf join3).contexts.length

def WireSuccClosureDocument.decode (wire : WireSuccClosureDocument) :
    Except String DecodedSuccClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB Succ-closure version {wire.version}"
  let join3 ← wire.join3_closure.decode
  let contexts ← wire.contexts.mapM (WireContextSuccClosure.decode join3)
  let actual := contexts.map (·.senderIndex.val)
  let expected := List.range (productionOf join3).contexts.length
  if hexact : actual = expected then
    return { join3, contexts, context_indices_exact := hexact }
  else throw "Succ closure does not cover every sender context exactly once"

def WireSuccClosureDocument.check (wire : WireSuccClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedContextSuccClosure.complete_delivery
    (context : DecodedContextSuccClosure join3) :
    ∀ offer ∈ directOffers join3.hyper.literalOrder
        ((productionOf join3).contexts.get context.senderIndex).retained,
      ∃ targetIndex strengtheningIndex,
        edgeDelivered join3 context.senderIndex.val targetIndex.val offer = true ∧
        Strengthens
          (((productionOf join3).contexts.get targetIndex).retained.get
            strengtheningIndex)
          (succHypothesis offer.pushed) := by
  intro offer hoffer
  rw [← context.offers_exact] at hoffer
  simp only [List.mem_map] at hoffer
  obtain ⟨coverage, _hcoverage, rfl⟩ := hoffer
  exact ⟨coverage.targetIndex, coverage.strengtheningIndex,
    coverage.edge_delivered, coverage.strengthens⟩

theorem WireSuccClosureDocument.check_sound
    (wire : WireSuccClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSuccClosureDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (·.senderIndex.val) =
        List.range (productionOf decoded.join3).contexts.length ∧
      ∀ context ∈ decoded.contexts,
        ∀ offer ∈ directOffers decoded.join3.hyper.literalOrder
            ((productionOf decoded.join3).contexts.get context.senderIndex).retained,
          ∃ targetIndex strengtheningIndex,
            edgeDelivered decoded.join3 context.senderIndex.val targetIndex.val offer = true ∧
            Strengthens
              (((productionOf decoded.join3).contexts.get targetIndex).retained.get
                strengtheningIndex)
              (succHypothesis offer.pushed) := by
  cases hdecode : wire.decode with
  | error message => simp [WireSuccClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.context_indices_exact, ?_⟩
      intro context _
      exact context.complete_delivery

#print axioms DecodedContextSuccClosure.complete_delivery
#print axioms WireSuccClosureDocument.check_sound

end ContextCalculus.CBSuccClosureWire
