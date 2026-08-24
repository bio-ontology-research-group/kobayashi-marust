import ContextCalculus.CBPredSendCoverageWire

/-!
# Executable CB terminal-state evidence

This layer checks the operational conditions under which KM may call a
production CB run complete. It does not infer closure merely from process
termination. The serialized state must show an empty global message queue, no
message or Nom truncation, an empty local todo queue in every context, no dirty
context, and complete semi-naive high-water marks for Pred, Succ, r-Succ, and
every predecessor edge.

The predecessor edge watermarks are compared with the exact pushed sets already
decoded by `CBPredSendCoverageWire`. A later Rust emitter binds these fields to
the live `Engine` and `Context` structures.
-/

namespace ContextCalculus.CBTerminalStateWire

open Lean ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBPredSendCoverageWire

structure WireTerminalContextState where
  context_index : Nat
  context_id : Nat
  todo_count : Nat
  dirty : Bool
  pred_pool_len : Nat
  pred_hwm : Nat
  succ_pool_len : Nat
  succ_hwm : Nat
  rsucc_pool_len : Nat
  rsucc_hwm : Nat
  rsucc_reach_len : Nat
  rsucc_offered : Nat
  rsucc_pair_reach_hwm : List Nat
  rsucc_edges_grew : Bool
  edge_seen : List Nat
deriving FromJson, ToJson

structure WireCBTerminalStateDocument where
  version : Nat
  send_coverage : WirePredSendCoverageDocument
  pending_messages : Nat
  message_truncated : Bool
  nominal_truncated : Bool
  contexts : List WireTerminalContextState
deriving FromJson, ToJson

/-- Lengths of the pushed sets on edges incoming to one receiver context.
The Rust `edge_seen` watermark belongs to the receiver's predecessor map, not
to the sender's outgoing-edge map.  Enumerating ordinary senders followed by
the optional root sender also matches the edge enumeration used by the live
state binding. -/
def incomingPushedLengthsAt (decoded : DecodedPredSendCoverageDocument)
    (receiverIndex : Nat) : List Nat :=
  let ordinary := decoded.senders.flatMap fun sender =>
    sender.edges.filterMap fun edge =>
      if edge.receiverIndex.val = receiverIndex then some edge.pushed.length else none
  let root := decoded.rootSender.toList.flatMap fun sender =>
    sender.edges.filterMap fun edge =>
      if edge.receiverIndex.val = receiverIndex then some edge.pushed.length else none
  ordinary ++ root

structure DecodedTerminalContextState
    (decoded : DecodedPredSendCoverageDocument) where
  contextIndex : Fin decoded.interContext.base.production.contexts.length
  contextId : Nat
  context_id_eq :
    (decoded.interContext.base.production.contexts.get contextIndex).contextId =
      contextId
  todo_count : Nat
  todo_empty : todo_count = 0
  dirty : Bool
  clean : dirty = false
  predPoolLen : Nat
  predHwm : Nat
  pred_complete : predHwm = predPoolLen
  succPoolLen : Nat
  succHwm : Nat
  succ_complete : succHwm = succPoolLen
  rsuccPoolLen : Nat
  rsuccHwm : Nat
  rsucc_complete : rsuccHwm = rsuccPoolLen
  rsuccReachLen : Nat
  rsuccOffered : Nat
  rsucc_reach_complete : rsuccOffered = rsuccReachLen
  rsuccPairReachHwm : List Nat
  rsucc_pairs_complete : ∀ watermark ∈ rsuccPairReachHwm,
    watermark = rsuccReachLen
  rsuccEdgesGrew : Bool
  rsucc_edges_stable : rsuccEdgesGrew = false
  edgeSeen : List Nat
  edge_watermarks_exact : edgeSeen = incomingPushedLengthsAt decoded contextIndex.val

def WireTerminalContextState.decode
    (decoded : DecodedPredSendCoverageDocument)
    (wire : WireTerminalContextState) :
    Except String (DecodedTerminalContextState decoded) := do
  if hindex : wire.context_index <
      decoded.interContext.base.production.contexts.length then
    let contextIndex : Fin decoded.interContext.base.production.contexts.length :=
      ⟨wire.context_index, hindex⟩
    let context := decoded.interContext.base.production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      if htodo : wire.todo_count = 0 then
        if hdirty : wire.dirty = false then
          if hpred : wire.pred_hwm = wire.pred_pool_len then
            if hsucc : wire.succ_hwm = wire.succ_pool_len then
              if hrsucc : wire.rsucc_hwm = wire.rsucc_pool_len then
                if hreach : wire.rsucc_offered = wire.rsucc_reach_len then
                  if hpairs : ∀ watermark ∈ wire.rsucc_pair_reach_hwm,
                      watermark = wire.rsucc_reach_len then
                    if hedgesStable : wire.rsucc_edges_grew = false then
                      let expectedEdges := incomingPushedLengthsAt decoded wire.context_index
                      if hedgeSeen : wire.edge_seen = expectedEdges then
                        return {
                        contextIndex
                        contextId := wire.context_id
                        context_id_eq := hid
                        todo_count := wire.todo_count
                        todo_empty := htodo
                        dirty := wire.dirty
                        clean := hdirty
                        predPoolLen := wire.pred_pool_len
                        predHwm := wire.pred_hwm
                        pred_complete := hpred
                        succPoolLen := wire.succ_pool_len
                        succHwm := wire.succ_hwm
                        succ_complete := hsucc
                        rsuccPoolLen := wire.rsucc_pool_len
                        rsuccHwm := wire.rsucc_hwm
                        rsucc_complete := hrsucc
                        rsuccReachLen := wire.rsucc_reach_len
                        rsuccOffered := wire.rsucc_offered
                        rsucc_reach_complete := hreach
                        rsuccPairReachHwm := wire.rsucc_pair_reach_hwm
                        rsucc_pairs_complete := hpairs
                        rsuccEdgesGrew := wire.rsucc_edges_grew
                        rsucc_edges_stable := hedgesStable
                        edgeSeen := wire.edge_seen
                        edge_watermarks_exact := hedgeSeen
                        }
                      else throw "CB terminal edge watermarks differ from pushed-set lengths"
                    else throw "CB terminal r-Succ edge-growth flag remains set"
                  else throw "CB terminal r-Succ pair high-water mark is incomplete"
                else throw "CB terminal r-Succ reach cross-product is incomplete"
              else throw "CB terminal r-Succ pool high-water mark is incomplete"
            else throw "CB terminal Succ pool high-water mark is incomplete"
          else throw "CB terminal Pred pool high-water mark is incomplete"
        else throw "CB terminal context remains dirty"
      else throw "CB terminal context has pending local clauses"
    else throw "CB terminal context id differs from its production context"
  else throw "CB terminal context index is outside the production run"

structure DecodedCBTerminalStateDocument where
  sendCoverage : DecodedPredSendCoverageDocument
  pendingMessages : Nat
  messages_empty : pendingMessages = 0
  messageTruncated : Bool
  messages_complete : messageTruncated = false
  nominalTruncated : Bool
  nom_complete : nominalTruncated = false
  contexts : List (DecodedTerminalContextState sendCoverage)
  context_indices_exact : contexts.map (fun context => context.contextIndex.val) =
    List.range sendCoverage.interContext.base.production.contexts.length

def WireCBTerminalStateDocument.decode (wire : WireCBTerminalStateDocument) :
    Except String DecodedCBTerminalStateDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB terminal-state version {wire.version}"
  let sendCoverage ← wire.send_coverage.decode
  if hmessages : wire.pending_messages = 0 then
    if hmessageComplete : wire.message_truncated = false then
      if hnomComplete : wire.nominal_truncated = false then
        let contexts ← wire.contexts.mapM
          (WireTerminalContextState.decode sendCoverage)
        let actual := contexts.map fun context => context.contextIndex.val
        let expected := List.range
          sendCoverage.interContext.base.production.contexts.length
        if hcontexts : actual = expected then
          return {
            sendCoverage
            pendingMessages := wire.pending_messages
            messages_empty := hmessages
            messageTruncated := wire.message_truncated
            messages_complete := hmessageComplete
            nominalTruncated := wire.nominal_truncated
            nom_complete := hnomComplete
            contexts
            context_indices_exact := hcontexts
          }
        else throw "CB terminal states do not cover every production context exactly once"
      else throw "CB terminal run exhausted the Nom allocation budget"
    else throw "CB terminal run truncated its message fixpoint"
  else throw "CB terminal run has pending inter-context messages"

def WireCBTerminalStateDocument.check (wire : WireCBTerminalStateDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

/-- Acceptance exposes the exact finite operational closure conditions. This is
the fairness boundary used by the production emitter: every finite local or
inter-context work item represented by these queues and high-water marks has
been consumed, and no budget discarded an item. -/
theorem WireCBTerminalStateDocument.check_sound
    (wire : WireCBTerminalStateDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCBTerminalStateDocument,
      wire.decode = .ok decoded ∧
      decoded.pendingMessages = 0 ∧
      decoded.messageTruncated = false ∧
      decoded.nominalTruncated = false ∧
      decoded.contexts.map (fun context => context.contextIndex.val) =
        List.range decoded.sendCoverage.interContext.base.production.contexts.length ∧
      ∀ context ∈ decoded.contexts,
        context.todo_count = 0 ∧ context.dirty = false ∧
        context.predHwm = context.predPoolLen ∧
        context.succHwm = context.succPoolLen ∧
        context.rsuccHwm = context.rsuccPoolLen ∧
        context.rsuccOffered = context.rsuccReachLen ∧
        (∀ watermark ∈ context.rsuccPairReachHwm,
          watermark = context.rsuccReachLen) ∧
        context.rsuccEdgesGrew = false ∧
        context.edgeSeen = incomingPushedLengthsAt decoded.sendCoverage
          context.contextIndex.val := by
  cases hdecode : wire.decode with
  | error message => simp [WireCBTerminalStateDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.messages_empty, decoded.messages_complete,
        decoded.nom_complete, decoded.context_indices_exact, ?_⟩
      intro context _
      exact ⟨context.todo_empty, context.clean, context.pred_complete,
        context.succ_complete, context.rsucc_complete,
        context.rsucc_reach_complete, context.rsucc_pairs_complete,
        context.rsucc_edges_stable,
        context.edge_watermarks_exact⟩

private def terminalContextExample : WireTerminalContextState where
  context_index := 0
  context_id := 7
  todo_count := 0
  dirty := false
  pred_pool_len := 1
  pred_hwm := 1
  succ_pool_len := 0
  succ_hwm := 0
  rsucc_pool_len := 0
  rsucc_hwm := 0
  rsucc_reach_len := 0
  rsucc_offered := 0
  rsucc_pair_reach_hwm := []
  rsucc_edges_grew := false
  edge_seen := [1]

def acceptedExample : WireCBTerminalStateDocument where
  version := 1
  send_coverage := CBPredSendCoverageWire.acceptedExample
  pending_messages := 0
  message_truncated := false
  nominal_truncated := false
  contexts := [terminalContextExample]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

example :
    ((WirePredSendCoverageDocument.decode
      ContextCalculus.CBPredSendCoverageWire.directedAcceptedExample).map fun decoded =>
      (incomingPushedLengthsAt decoded 0, incomingPushedLengthsAt decoded 1)) =
      Except.ok ([], [1]) := by
  native_decide

example : rejected ({ acceptedExample with pending_messages := 1 }).check = true := by
  native_decide

example : rejected ({ acceptedExample with message_truncated := true }).check = true := by
  native_decide

example : rejected ({ acceptedExample with contexts :=
    [{ terminalContextExample with pred_hwm := 0 }] }).check = true := by
  native_decide

example : rejected ({ acceptedExample with contexts :=
    [{ terminalContextExample with edge_seen := [0] }] }).check = true := by
  native_decide

#print axioms WireCBTerminalStateDocument.check_sound

end ContextCalculus.CBTerminalStateWire
