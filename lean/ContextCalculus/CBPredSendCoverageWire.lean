import ContextCalculus.CBPredSendEnumeration
import ContextCalculus.CBRootPredSendEnumeration
import ContextCalculus.CBInterContextWire
import ContextCalculus.CBNominalAllocationWire

/-!
# Exact ordinary-Pred transfer-list coverage

This checker recomputes Pred sender eligibility from every terminal context
snapshot. Ordinary contexts use the per-edge condition. The nominal ground
context uses the exact two-branch r-Pred condition: x-free clauses may discharge
different body atoms over different individual-labelled edges of one receiver,
while x-containing clauses retain the per-edge path. For every sender it
derives the exact destination and backward substitution and requires the
referenced transfer subsequence to have exactly those signatures. The ordinary
and root subsequences together partition every transfer exactly once.

The ground-context designation and predecessor snapshots still have to be
bound to KM's terminal Rust state.
-/

namespace ContextCalculus.CBPredSendCoverageWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBInterContextWire ContextCalculus.CBPredSendEnumeration
open ContextCalculus.CBRootPredSendEnumeration
open ContextCalculus.CBSourceWire
open ContextCalculus.CBNominalAllocationWire

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
  root_sender : Option WirePredSenderSnapshot
  nominal_allocation : Option WireNominalAllocation
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
      let label ← wire.label.decode production.bounds
      if hlabel : ordinaryLabel label = true then
        if _hwireNodup : wire.pushed.Nodup then
          let pushed ← wire.pushed.mapM
            (WirePredicate.decode production.bounds)
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

structure DecodedRootPredEdge (production : DecodedProductionRun) where
  receiverIndex : Fin production.contexts.length
  receiverId : Nat
  receiver_id_eq :
    (production.contexts.get receiverIndex).contextId = receiverId
  individual : Nat
  individual_lt : individual < production.bounds.individuals
  pushed : List FPred
  pushed_nodup : pushed.Nodup

def WirePredEdge.decodeRoot (production : DecodedProductionRun)
    (wire : WirePredEdge) : Except String (DecodedRootPredEdge production) := do
  if hreceiver : wire.receiver_context_index < production.contexts.length then
    let receiverIndex : Fin production.contexts.length :=
      ⟨wire.receiver_context_index, hreceiver⟩
    let receiver := production.contexts.get receiverIndex
    if hid : receiver.contextId = wire.receiver_context_id then
      let label ← wire.label.decode production.bounds
      match label with
      | .const individual =>
          if hindividual : individual < production.bounds.individuals then
            if _hwireNodup : wire.pushed.Nodup then
              let pushed ← wire.pushed.mapM
                (WirePredicate.decode production.bounds)
              if hpushedNodup : pushed.Nodup then
                return {
                  receiverIndex
                  receiverId := wire.receiver_context_id
                  receiver_id_eq := hid
                  individual
                  individual_lt := hindividual
                  pushed
                  pushed_nodup := hpushedNodup
                }
              else throw "decoded root Pred edge pushed set contains duplicates"
            else throw "root Pred edge pushed set contains duplicates"
          else throw "root Pred edge individual is outside the runtime table"
      | _ => throw "root Pred edge label is not an individual"
    else throw "root Pred edge receiver id differs from its indexed context"
  else throw "root Pred edge receiver-context index is outside the production run"

def DecodedPredEdge.toPredEdge
    (edge : DecodedPredEdge production) : PredEdge :=
  { receiverIndex := edge.receiverIndex.val
    label := edge.label
    pushed := edge.pushed }

def DecodedRootPredEdge.toRootPredEdge
    (edge : DecodedRootPredEdge production) : RootPredEdge :=
  { receiverIndex := edge.receiverIndex.val
    individual := edge.individual
    pushed := edge.pushed }

structure TransferSignature where
  senderIndex : Nat
  receiverIndex : Nat
  retainedIndex : Nat
  substitution : List (Int × FTerm)
deriving DecidableEq, Repr

def ordinarySubstitution (label : FTerm) : List (Int × FTerm) :=
  [(-1, .var 0), (0, label)]

def rootSubstitution (individual : Nat) : List (Int × FTerm) :=
  [(-1, .var 0), (0, .const individual)]

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

def expectedRootSignatures
    (production : DecodedProductionRun)
    (senderIndex : Fin production.contexts.length)
    (edges : List (DecodedRootPredEdge production)) : List TransferSignature :=
  let sender := production.contexts.get senderIndex
  let plainEdges := edges.map DecodedRootPredEdge.toRootPredEdge
  (enumerateAll production.source.bounds.individuals sender.retained plainEdges).filterMap
    fun key => do
      let edge ← edges[key.edgeIndex]?
      return {
        senderIndex := senderIndex.val
        receiverIndex := edge.receiverIndex.val
        retainedIndex := key.retainedIndex
        substitution := rootSubstitution edge.individual
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

def rootTransferIndices (decoded : DecodedCompleteInterContextRun)
    (groundContextIndex : Nat) : List Nat :=
  (List.range decoded.base.transfers.length).filter fun index =>
    match decoded.base.transfers[index]? with
    | some transfer => decide (transfer.senderIndex.val = groundContextIndex)
    | none => false

def rootContextIndices (production : DecodedProductionRun) : List Nat :=
  (List.range production.contexts.length).filter fun index =>
    match production.contexts[index]? with
    | some context => context.root
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

structure DecodedRootPredSenderSnapshot
    (decoded : DecodedCompleteInterContextRun) where
  senderIndex : Fin decoded.base.production.contexts.length
  senderId : Nat
  sender_id_eq :
    (decoded.base.production.contexts.get senderIndex).contextId = senderId
  edges : List (DecodedRootPredEdge decoded.base.production)
  transferIndices : List (Fin decoded.base.transfers.length)
  signatures_exact :
    transferIndices.map (fun index =>
      transferSignature (decoded.base.transfers.get index)) =
    expectedRootSignatures decoded.base.production senderIndex edges

def WirePredSenderSnapshot.decodeRoot
    (decoded : DecodedCompleteInterContextRun)
    (groundIndex : Fin decoded.base.production.contexts.length)
    (wire : WirePredSenderSnapshot) :
    Except String (DecodedRootPredSenderSnapshot decoded) := do
  if hsender : wire.sender_context_index = groundIndex.val then
    let sender := decoded.base.production.contexts.get groundIndex
    if hid : sender.contextId = wire.sender_context_id then
      let edges ← wire.edges.mapM (WirePredEdge.decodeRoot decoded.base.production)
      let transferIndices ← wire.transfer_indices.mapM fun index =>
        if hindex : index < decoded.base.transfers.length then
          pure (⟨index, hindex⟩ : Fin decoded.base.transfers.length)
        else throw "root Pred transfer index is outside the transfer list"
      let actual := transferIndices.map fun index =>
        transferSignature (decoded.base.transfers.get index)
      let expected := expectedRootSignatures decoded.base.production groundIndex edges
      if hexact : actual = expected then
        return {
          senderIndex := groundIndex
          senderId := wire.sender_context_id
          sender_id_eq := hid
          edges
          transferIndices
          signatures_exact := hexact
        }
      else throw "root Pred transfers differ from exact eligible sends"
    else throw "root Pred sender id differs from its indexed context"
  else throw "root Pred sender index differs from the designated ground context"

structure DecodedBoundNominalAllocation
    (production : DecodedProductionRun) where
  allocation : DecodedNominalAllocation
  source_bounds_eq : allocation.source.bounds = production.source.bounds
  source_ontology_eq : allocation.source.ontology = production.source.ontology
  runtime_count_eq : allocation.individualCount = production.bounds.individuals

def decodeBoundNominalAllocation (production : DecodedProductionRun)
    (wire : WireNominalAllocation) :
    Except String (DecodedBoundNominalAllocation production) := do
  let allocation ← wire.decode
  if hbounds : allocation.source.bounds = production.source.bounds then
    if hontology : allocation.source.ontology = production.source.ontology then
      if hcount : allocation.individualCount = production.bounds.individuals then
        return {
          allocation
          source_bounds_eq := hbounds
          source_ontology_eq := hontology
          runtime_count_eq := hcount
        }
      else throw "Nom allocation runtime bound differs from the production trace"
    else throw "Nom allocation ontology differs from the production trace"
  else throw "Nom allocation source bounds differ from the production trace"

structure DecodedNominalAllocationBinding
    (production : DecodedProductionRun) where
  allocation : Option (DecodedBoundNominalAllocation production)
  present_iff : production.source.bounds.individuals <
      production.bounds.individuals ↔ allocation.isSome = true

def decodeNominalAllocationBinding (production : DecodedProductionRun)
    (wire : Option WireNominalAllocation) :
    Except String (DecodedNominalAllocationBinding production) := do
  if hextended : production.source.bounds.individuals <
      production.bounds.individuals then
    match wire with
    | some allocationWire =>
        let allocation ← decodeBoundNominalAllocation production allocationWire
        return {
          allocation := some allocation
          present_iff := by simp [hextended]
        }
    | none => throw "extended runtime individual table has no Nom allocation evidence"
  else
    match wire with
    | none =>
        return {
          allocation := none
          present_iff := by simp [hextended]
        }
    | some _ => throw "Nom allocation evidence exists without fresh runtime individuals"

structure DecodedPredSendCoverageDocument where
  interContext : DecodedCompleteInterContextRun
  groundContextIndex : Option Nat
  ground_index_valid : ∀ index ∈ groundContextIndex,
    index < interContext.base.production.contexts.length
  ground_index_exact : groundContextIndex.toList =
    rootContextIndices interContext.base.production
  senders : List (DecodedPredSenderSnapshot interContext)
  rootSender : Option (DecodedRootPredSenderSnapshot interContext)
  nominalAllocation : Option
    (DecodedBoundNominalAllocation interContext.base.production)
  sender_indices_exact : senders.map (fun sender => sender.senderIndex.val) =
    ordinarySenderIndices interContext.base.production.contexts.length
      groundContextIndex
  transfer_partition_exact : senders.flatMap (fun sender =>
      sender.transferIndices.map Fin.val) =
    ordinaryTransferIndices interContext groundContextIndex
  root_sender_present : groundContextIndex.isSome = rootSender.isSome
  root_transfer_partition_exact : rootSender.toList.flatMap (fun sender =>
      sender.transferIndices.map Fin.val) =
    groundContextIndex.toList.flatMap (rootTransferIndices interContext)
  allocation_present_iff :
    interContext.base.production.source.bounds.individuals <
        interContext.base.production.bounds.individuals ↔
      nominalAllocation.isSome = true

def WirePredSendCoverageDocument.decode
    (wire : WirePredSendCoverageDocument) :
    Except String DecodedPredSendCoverageDocument := do
  if wire.version != 2 then
    throw s!"unsupported CB Pred send-coverage version {wire.version}"
  let interContext ← wire.inter_context.decode
  let allocationBinding ← decodeNominalAllocationBinding
    interContext.base.production wire.nominal_allocation
  if hground : ∀ index ∈ wire.ground_context_index,
      index < interContext.base.production.contexts.length then
    if hgroundExact : wire.ground_context_index.toList =
        rootContextIndices interContext.base.production then
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
        match hcase : wire.ground_context_index, wire.root_sender with
        | none, none =>
            return {
              interContext
              groundContextIndex := none
              ground_index_valid := by simpa [hcase] using hground
              ground_index_exact := by simpa [hcase] using hgroundExact
              senders
              rootSender := none
              nominalAllocation := allocationBinding.allocation
              sender_indices_exact := by
                simpa [actualSenders, expectedSenders, hcase] using hsenders
              transfer_partition_exact := by
                simpa [actualTransfers, expectedTransfers, hcase] using htransfers
              root_sender_present := rfl
              root_transfer_partition_exact := rfl
              allocation_present_iff := allocationBinding.present_iff
            }
        | some groundIndex, some rootWire =>
            have hindex : groundIndex < interContext.base.production.contexts.length :=
              hground groundIndex (by simp [hcase])
            let rootSender ← rootWire.decodeRoot interContext ⟨groundIndex, hindex⟩
            let actualRoot := rootSender.transferIndices.map Fin.val
            let expectedRoot := rootTransferIndices interContext groundIndex
            if hroot : actualRoot = expectedRoot then
              return {
                interContext
                groundContextIndex := some groundIndex
                ground_index_valid := by simpa [hcase] using hground
                ground_index_exact := by simpa [hcase] using hgroundExact
                senders
                rootSender := some rootSender
                nominalAllocation := allocationBinding.allocation
                sender_indices_exact := by
                  simpa [actualSenders, expectedSenders, hcase] using hsenders
                transfer_partition_exact := by
                  simpa [actualTransfers, expectedTransfers, hcase] using htransfers
                root_sender_present := rfl
                root_transfer_partition_exact := by simpa using hroot
                allocation_present_iff := allocationBinding.present_iff
              }
            else throw "root Pred snapshot does not partition every ground-context transfer"
        | none, some _ =>
            throw "root Pred snapshot exists without a designated ground context"
        | some _, none =>
            throw "designated ground context has no root Pred snapshot"
      else throw "ordinary Pred sender snapshots do not partition all ordinary transfers"
    else throw "ordinary Pred snapshots do not cover every non-ground sender exactly once"
    else throw "designated ground context differs from the unique root context"
  else throw "nominal ground-context index is outside the production run"

def WirePredSendCoverageDocument.check
    (wire : WirePredSendCoverageDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WirePredSendCoverageDocument.check_sound
    (wire : WirePredSendCoverageDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedPredSendCoverageDocument,
      wire.decode = .ok decoded ∧
      decoded.groundContextIndex.toList =
        rootContextIndices decoded.interContext.base.production ∧
      decoded.senders.map (fun sender => sender.senderIndex.val) =
        ordinarySenderIndices decoded.interContext.base.production.contexts.length
          decoded.groundContextIndex ∧
      decoded.senders.flatMap (fun sender =>
          sender.transferIndices.map Fin.val) =
        ordinaryTransferIndices decoded.interContext decoded.groundContextIndex ∧
      decoded.rootSender.toList.flatMap (fun sender =>
          sender.transferIndices.map Fin.val) =
        decoded.groundContextIndex.toList.flatMap
          (rootTransferIndices decoded.interContext) ∧
      (decoded.interContext.base.production.source.bounds.individuals <
          decoded.interContext.base.production.bounds.individuals ↔
        decoded.nominalAllocation.isSome = true) ∧
      (∀ sender ∈ decoded.senders,
        sender.transferIndices.map (fun index =>
          transferSignature (decoded.interContext.base.transfers.get index)) =
        expectedSignatures decoded.interContext.base.production
          sender.senderIndex sender.edges) ∧
      (∀ sender ∈ decoded.rootSender,
        sender.transferIndices.map (fun index =>
          transferSignature (decoded.interContext.base.transfers.get index)) =
        expectedRootSignatures decoded.interContext.base.production
          sender.senderIndex sender.edges) := by
  cases hdecode : wire.decode with
  | error message => simp [WirePredSendCoverageDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.ground_index_exact, decoded.sender_indices_exact,
        decoded.transfer_partition_exact, decoded.root_transfer_partition_exact,
        decoded.allocation_present_iff, ?_, ?_⟩
      · intro sender _
        exact sender.signatures_exact
      · intro sender hsender
        simpa [hsender] using sender.signatures_exact

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
  individual_count := 0
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
  version := 2
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
  root_sender := none
  nominal_allocation := none

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

private def allocationKeyExample : WireNominalFiringKey where
  context := 7
  source_index := 0
  source_body := [concept 0]
  source_head := [literal 1]
  side_body := []
  side_head := []
  selected := [(0, .concept 0 (.constant 0))]
  substitution := [{ variableId := 0, term := .constant 0 }]

private def allocationExample : WireNominalAllocation where
  version := 1
  source := sourceExample
  individual_count := 1
  budget := 1
  allocated := 1
  truncated := false
  blocks := [{
    key := allocationKeyExample
    first := 0
    width := 1
    body := []
    kept_head := []
    conclusion := ⟨[], [.equality (.var (-1)) (.constant 0)]⟩
  }]

private def acceptedAllocationExample : WirePredSendCoverageDocument :=
  { acceptedExample with
    inter_context := {
      interContextExample with
      production := { productionExample with individual_count := 1 }
    }
    nominal_allocation := some allocationExample }

example : acceptedAllocationExample.check = .ok true := by native_decide

example : rejected
    ({ acceptedAllocationExample with nominal_allocation := none }).check = true := by
  native_decide

private def rootSourceExample : WireSourceBinding :=
  { sourceExample with individual_count := 1 }

private def rootContextExample : WireProductionContext :=
  { contextExample with context_id := 9, root := true, core := [] }

private def rootProductionExample : WireProductionRun where
  version := 1
  source := rootSourceExample
  individual_count := 1
  contexts := [rootContextExample]

private def rootInterContextExample : WireInterContextRun where
  version := 1
  production := rootProductionExample
  transfers := [{
    sender_context_index := 0
    sender_context_id := 9
    receiver_context_index := 0
    receiver_context_id := 9
    retained_clause_index := 0
    substitution := [
      { variableId := -1, term := x },
      { variableId := 0, term := .constant 0 }]
    payload := ⟨
      [.predicate (.concept 0 (.constant 0))],
      [.predicate (.concept 1 (.constant 0))]⟩
  }]
  arrivals := []

private def acceptedRootExample : WirePredSendCoverageDocument where
  version := 2
  inter_context := rootInterContextExample
  ground_context_index := some 0
  senders := []
  root_sender := some {
    sender_context_index := 0
    sender_context_id := 9
    edges := [{
      receiver_context_index := 0
      receiver_context_id := 9
      label := .constant 0
      pushed := [concept 0]
    }]
    transfer_indices := [0]
  }
  nominal_allocation := none

example : acceptedRootExample.check = .ok true := by native_decide

example : rejected ({ acceptedRootExample with root_sender := none }).check = true := by
  native_decide

private def missingRootMarkerExample : WirePredSendCoverageDocument :=
  { acceptedRootExample with
    inter_context := {
      rootInterContextExample with
      production := {
        rootProductionExample with
        contexts := [{ rootContextExample with root := false }]
      }
    } }

example : rejected missingRootMarkerExample.check = true := by native_decide

private def badRootLabelExample : WirePredSendCoverageDocument :=
  { acceptedRootExample with
    root_sender := acceptedRootExample.root_sender.map fun sender =>
      { sender with edges := sender.edges.map fun edge =>
          { edge with label := fx } } }

example : rejected badRootLabelExample.check = true := by native_decide

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
