import ContextCalculus.CBPredSendEnumeration
import ContextCalculus.CBInterContextWire

/-!
# Exact ordinary-Pred transfer-list coverage

This checker recomputes ordinary Pred sender eligibility from every non-ground
terminal context snapshot.  For each sender it enumerates all retained-clause
and predecessor-edge pairs, derives their exact destination and backward
substitution, and requires the referenced transfer subsequence to have exactly
those signatures.  It also requires the snapshot transfer indexes to partition
all transfers whose sender is not the designated nominal ground context.

The ground-context designation and the edge snapshots still have to be bound
to KM's terminal Rust state.  Nominal r-Pred is intentionally excluded here;
its eligibility uses the separate multi-edge individual-discharge condition.
-/

namespace ContextCalculus.CBPredSendCoverageWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBInterContextWire ContextCalculus.CBPredSendEnumeration
open ContextCalculus.CBSourceWire

structure WirePredEdge where
  receiver_context_index : Nat
  receiver_context_id : Nat
  label : WireTerm
  pushed : List WirePredicate
deriving FromJson, ToJson

structure WirePredSenderSnapshot where
  sender_context_index : Nat
  sender_context_id : Nat
  edges : List WirePredEdge
  transfer_indices : List Nat
deriving FromJson, ToJson

structure WirePredSendCoverageDocument where
  version : Nat
  inter_context : WireInterContextRun
  ground_context_index : Option Nat
  senders : List WirePredSenderSnapshot
deriving FromJson, ToJson

def ordinaryLabel : FTerm → Bool
  | .app _ (.var 0) => true
  | _ => false

structure DecodedPredEdge (production : DecodedProductionRun) where
  receiverIndex : Fin production.contexts.length
  receiverId : Nat
  receiver_id_eq :
    (production.contexts.get receiverIndex).contextId = receiverId
  label : FTerm
  label_ordinary : ordinaryLabel label = true
  pushed : List FPred
  pushed_nodup : pushed.Nodup

def WirePredEdge.decode (production : DecodedProductionRun)
    (wire : WirePredEdge) : Except String (DecodedPredEdge production) := do
  if hreceiver : wire.receiver_context_index < production.contexts.length then
    let receiverIndex : Fin production.contexts.length :=
      ⟨wire.receiver_context_index, hreceiver⟩
    let receiver := production.contexts.get receiverIndex
    if hid : receiver.contextId = wire.receiver_context_id then
      let label ← wire.label.decode production.source.bounds
      if hlabel : ordinaryLabel label = true then
        if _hwireNodup : wire.pushed.Nodup then
          let pushed ← wire.pushed.mapM
            (WirePredicate.decode production.source.bounds)
          if hpushedNodup : pushed.Nodup then
            return {
              receiverIndex
              receiverId := wire.receiver_context_id
              receiver_id_eq := hid
              label
              label_ordinary := hlabel
              pushed
              pushed_nodup := hpushedNodup
            }
          else throw "decoded Pred edge pushed set contains duplicates"
        else throw "Pred edge pushed set contains duplicates"
      else throw "ordinary Pred edge label is not f(x)"
    else throw "Pred edge receiver id differs from its indexed context"
  else throw "Pred edge receiver-context index is outside the production run"

def DecodedPredEdge.toPredEdge
    (edge : DecodedPredEdge production) : PredEdge :=
  { receiverIndex := edge.receiverIndex.val
    label := edge.label
    pushed := edge.pushed }

structure TransferSignature where
  senderIndex : Nat
  receiverIndex : Nat
  retainedIndex : Nat
  substitution : List (Int × FTerm)
deriving DecidableEq, Repr

def ordinarySubstitution (label : FTerm) : List (Int × FTerm) :=
  [(-1, .var 0), (0, label)]

def expectedSignatures
    (production : DecodedProductionRun)
    (senderIndex : Fin production.contexts.length)
    (edges : List (DecodedPredEdge production)) : List TransferSignature :=
  let sender := production.contexts.get senderIndex
  let plainEdges := edges.map DecodedPredEdge.toPredEdge
  (enumerate sender.retained plainEdges).filterMap fun key => do
    let edge ← edges[key.edgeIndex]?
    return {
      senderIndex := senderIndex.val
      receiverIndex := edge.receiverIndex.val
      retainedIndex := key.retainedIndex
      substitution := ordinarySubstitution edge.label
    }

def transferSignature (transfer : DecodedPredTransfer production) :
    TransferSignature :=
  { senderIndex := transfer.senderIndex.val
    receiverIndex := transfer.receiverIndex.val
    retainedIndex := transfer.retainedIndex.val
    substitution := transfer.substitution }

def ordinarySenderIndices (contextCount : Nat)
    (groundContextIndex : Option Nat) : List Nat :=
  (List.range contextCount).filter fun index =>
    decide (groundContextIndex ≠ some index)

def ordinaryTransferIndices (decoded : DecodedCompleteInterContextRun)
    (groundContextIndex : Option Nat) : List Nat :=
  (List.range decoded.base.transfers.length).filter fun index =>
    match decoded.base.transfers[index]? with
    | some transfer => decide (groundContextIndex ≠ some transfer.senderIndex.val)
    | none => false

structure DecodedPredSenderSnapshot
    (decoded : DecodedCompleteInterContextRun) where
  senderIndex : Fin decoded.base.production.contexts.length
  senderId : Nat
  sender_id_eq :
    (decoded.base.production.contexts.get senderIndex).contextId = senderId
  edges : List (DecodedPredEdge decoded.base.production)
  transferIndices : List (Fin decoded.base.transfers.length)
  signatures_exact :
    transferIndices.map (fun index =>
      transferSignature (decoded.base.transfers.get index)) =
    expectedSignatures decoded.base.production senderIndex edges

def WirePredSenderSnapshot.decode (decoded : DecodedCompleteInterContextRun)
    (wire : WirePredSenderSnapshot) :
    Except String (DecodedPredSenderSnapshot decoded) := do
  if hsender : wire.sender_context_index < decoded.base.production.contexts.length then
    let senderIndex : Fin decoded.base.production.contexts.length :=
      ⟨wire.sender_context_index, hsender⟩
    let sender := decoded.base.production.contexts.get senderIndex
    if hid : sender.contextId = wire.sender_context_id then
      let edges ← wire.edges.mapM (WirePredEdge.decode decoded.base.production)
      let transferIndices ← wire.transfer_indices.mapM fun index =>
        if hindex : index < decoded.base.transfers.length then
          pure (⟨index, hindex⟩ : Fin decoded.base.transfers.length)
        else throw "ordinary Pred transfer index is outside the transfer list"
      let actual := transferIndices.map fun index =>
        transferSignature (decoded.base.transfers.get index)
      let expected := expectedSignatures decoded.base.production senderIndex edges
      if hexact : actual = expected then
        return {
          senderIndex
          senderId := wire.sender_context_id
          sender_id_eq := hid
          edges
          transferIndices
          signatures_exact := hexact
        }
      else throw "ordinary Pred transfers differ from exact eligible sends"
    else throw "ordinary Pred sender id differs from its indexed context"
  else throw "ordinary Pred sender-context index is outside the production run"

structure DecodedPredSendCoverageDocument where
  interContext : DecodedCompleteInterContextRun
  groundContextIndex : Option Nat
  ground_index_valid : ∀ index ∈ groundContextIndex,
    index < interContext.base.production.contexts.length
  senders : List (DecodedPredSenderSnapshot interContext)
  sender_indices_exact : senders.map (fun sender => sender.senderIndex.val) =
    ordinarySenderIndices interContext.base.production.contexts.length
      groundContextIndex
  transfer_partition_exact : senders.flatMap (fun sender =>
      sender.transferIndices.map Fin.val) =
    ordinaryTransferIndices interContext groundContextIndex

def WirePredSendCoverageDocument.decode
    (wire : WirePredSendCoverageDocument) :
    Except String DecodedPredSendCoverageDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB Pred send-coverage version {wire.version}"
  let interContext ← wire.inter_context.decode
  if hground : ∀ index ∈ wire.ground_context_index,
      index < interContext.base.production.contexts.length then
    let senders ← wire.senders.mapM
      (WirePredSenderSnapshot.decode interContext)
    let actualSenders := senders.map fun sender => sender.senderIndex.val
    let expectedSenders := ordinarySenderIndices
      interContext.base.production.contexts.length wire.ground_context_index
    if hsenders : actualSenders = expectedSenders then
      let actualTransfers := senders.flatMap fun sender =>
        sender.transferIndices.map Fin.val
      let expectedTransfers := ordinaryTransferIndices interContext
        wire.ground_context_index
      if htransfers : actualTransfers = expectedTransfers then
        return {
          interContext
          groundContextIndex := wire.ground_context_index
          ground_index_valid := hground
          senders
          sender_indices_exact := hsenders
          transfer_partition_exact := htransfers
        }
      else throw "ordinary Pred sender snapshots do not partition all ordinary transfers"
    else throw "ordinary Pred snapshots do not cover every non-ground sender exactly once"
  else throw "nominal ground-context index is outside the production run"

def WirePredSendCoverageDocument.check
    (wire : WirePredSendCoverageDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WirePredSendCoverageDocument.check_sound
    (wire : WirePredSendCoverageDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedPredSendCoverageDocument,
      wire.decode = .ok decoded ∧
      decoded.senders.map (fun sender => sender.senderIndex.val) =
        ordinarySenderIndices decoded.interContext.base.production.contexts.length
          decoded.groundContextIndex ∧
      decoded.senders.flatMap (fun sender =>
          sender.transferIndices.map Fin.val) =
        ordinaryTransferIndices decoded.interContext decoded.groundContextIndex ∧
      ∀ sender ∈ decoded.senders,
        sender.transferIndices.map (fun index =>
          transferSignature (decoded.interContext.base.transfers.get index)) =
        expectedSignatures decoded.interContext.base.production
          sender.senderIndex sender.edges := by
  cases hdecode : wire.decode with
  | error message => simp [WirePredSendCoverageDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.sender_indices_exact,
        decoded.transfer_partition_exact, ?_⟩
      intro sender _
      exact sender.signatures_exact

private def x : WireTerm := .var 0
private def fx : WireTerm := .app 0 x
private def concept (id : Nat) : WirePredicate := .concept id x
private def literal (id : Nat) : WireLiteral := .predicate (concept id)

private def sourceExample : WireSourceBinding where
  version := 1
  concept_count := 2
  role_count := 0
  function_count := 1
  individual_count := 0
  source_clauses := [.gci [0] [1]]
  role_chains := []
  ontology := [⟨[literal 0], [literal 1]⟩]

private def contextExample : WireProductionContext where
  context_id := 7
  root := false
  query_concept := none
  core := [concept 0]
  retained := [⟨[literal 0], [literal 1]⟩]
  discarded := []
  trace := [⟨⟨[literal 0], [literal 1]⟩, .premise 0 []⟩]

private def productionExample : WireProductionRun where
  version := 1
  source := sourceExample
  contexts := [contextExample]

private def interContextExample : WireInterContextRun where
  version := 1
  production := productionExample
  transfers := [{
    sender_context_index := 0
    sender_context_id := 7
    receiver_context_index := 0
    receiver_context_id := 7
    retained_clause_index := 0
    substitution := [
      { variableId := -1, term := x },
      { variableId := 0, term := fx }]
    payload := ⟨
      [.predicate (.concept 0 fx)],
      [.predicate (.concept 1 fx)]⟩
  }]
  arrivals := []

def acceptedExample : WirePredSendCoverageDocument where
  version := 1
  inter_context := interContextExample
  ground_context_index := none
  senders := [{
    sender_context_index := 0
    sender_context_id := 7
    edges := [{
      receiver_context_index := 0
      receiver_context_id := 7
      label := fx
      pushed := [concept 0]
    }]
    transfer_indices := [0]
  }]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

private def omittedTransferExample : WirePredSendCoverageDocument :=
  { acceptedExample with senders := acceptedExample.senders.map fun sender =>
      { sender with transfer_indices := [] } }

example : rejected omittedTransferExample.check = true := by native_decide

private def forgedEdgeCoverageExample : WirePredSendCoverageDocument :=
  { acceptedExample with senders := acceptedExample.senders.map fun sender =>
      { sender with edges := sender.edges.map fun edge =>
          { edge with pushed := [] } } }

example : rejected forgedEdgeCoverageExample.check = true := by native_decide

#print axioms WirePredSendCoverageDocument.check_sound

end ContextCalculus.CBPredSendCoverageWire
