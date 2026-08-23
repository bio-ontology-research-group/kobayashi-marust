import ContextCalculus.CBGlobalModelWire

/-!
# Exact binding to KM's compact live CB state

The production engine stores terms as packed `UInt32` values and retained
clauses as indices into separate ordinary and root-context arenas.  This wire
decodes that representation independently and requires every live context to
name exactly the retained clauses in the already source-bound global model
document.  A certificate for another run therefore cannot be paired with a
live snapshot merely by reusing context identifiers.
-/

namespace ContextCalculus.CBLiveStateWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBGlobalClosureWire
open ContextCalculus.CBGlobalModelWire

private def xRaw : Nat := 65535
private def yRaw : Nat := 65534
private def functionBase : Nat := 1048576
private def compositeBase : Nat := 4194304

structure WireLiveLiteral where
  kind : String
  iri : Option Nat
  first : Nat
  second : Option Nat
deriving FromJson, ToJson

structure WireLiveClause where
  body : List WireLiveLiteral
  head : List WireLiveLiteral
deriving FromJson, ToJson

structure WireLivePredicate where
  kind : String
  iri : Nat
  first : Nat
  second : Option Nat
deriving FromJson, ToJson

structure WireLivePredecessorEdge where
  predecessor_context : Nat
  label : Nat
  pushed : List WireLivePredicate
  pred_pool_seen : List Nat
  edge_seen : Nat
deriving FromJson, ToJson

structure WireLiveSuccessorEdge where
  label : Nat
  target_context : Nat
  rsucc_reach_hwm : Nat
deriving FromJson, ToJson

structure WireLiveInsertionEvent where
  sequence : Nat
  context_index : Nat
  root : Bool
  clause_id : Nat
deriving FromJson, ToJson

structure WireLiveContext where
  context_index : Nat
  context_id : Nat
  root : Bool
  retained_clause_ids : List Nat
  todo_clause_ids : List Nat
  dirty : Bool
  pred_pool_ids : List Nat
  pred_hwm : Nat
  succ_pool_ids : List Nat
  succ_hwm : Nat
  rsucc_pool_ids : List Nat
  rsucc_hwm : Nat
  rsucc_reach : List WireLivePredicate
  rsucc_offered : Nat
  rsucc_edges_grew : Bool
  predecessor_edge_seen : List Nat
  successor_reach_hwm : List Nat
  predecessors : List WireLivePredecessorEdge
  successors : List WireLiveSuccessorEdge
deriving FromJson, ToJson

structure WireLiveStateDocument where
  version : Nat
  comp_ind_bits : Nat
  rsucc_enabled : Bool
  reach_concept_ids : List Nat
  pending_messages : Nat
  message_truncated : Bool
  nominal_truncated : Bool
  ordinary_clause_arena : List WireLiveClause
  root_clause_arena : List WireLiveClause
  insertion_history : List WireLiveInsertionEvent
  contexts : List WireLiveContext
deriving FromJson, ToJson

def decodeRawTerm (bounds : Bounds) (bits raw : Nat) : Except String FTerm := do
  if bits = 0 ∨ 32 ≤ bits then
    throw "CB live packed-individual width is outside 1..31"
  if raw = xRaw then return .var 0
  if raw ≤ yRaw then return .var (Int.ofNat raw - Int.ofNat xRaw)
  if raw < functionBase then
    return .const (← checkId "CB live individual" bounds.individuals (raw - xRaw))
  if raw < compositeBase then
    return .app (← checkId "CB live function" bounds.functions
      (raw - functionBase)) (.var 0)
  let packed := raw - compositeBase
  let radix := 2 ^ bits
  let functionId := packed / radix
  let individualId := packed % radix
  return .app (← checkId "CB live composite function" bounds.functions functionId)
    (.const (← checkId "CB live composite individual"
      bounds.individuals individualId))

def WireLiveLiteral.decode (bounds : Bounds) (bits : Nat)
    (wire : WireLiveLiteral) : Except String FLit := do
  let first ← decodeRawTerm bounds bits wire.first
  match wire.kind, wire.iri, wire.second with
  | "concept", some iri, none =>
      return .P (.concept (← checkId "CB live concept" bounds.concepts iri) first)
  | "role", some iri, some second =>
      return .P (.role (← checkId "CB live role" bounds.roles iri) first
        (← decodeRawTerm bounds bits second))
  | "equality", none, some second =>
      return .eq first (← decodeRawTerm bounds bits second)
  | "inequality", none, some second =>
      return .ineq first (← decodeRawTerm bounds bits second)
  | _, _, _ => throw "malformed CB live literal"

def WireLivePredicate.decode (bounds : Bounds) (bits : Nat)
    (wire : WireLivePredicate) : Except String FPred := do
  let first ← decodeRawTerm bounds bits wire.first
  match wire.kind, wire.second with
  | "concept", none =>
      return .concept (← checkId "CB live concept" bounds.concepts wire.iri) first
  | "role", some second =>
      return .role (← checkId "CB live role" bounds.roles wire.iri) first
        (← decodeRawTerm bounds bits second)
  | _, _ => throw "malformed CB live predicate"

def WireLiveClause.decode (bounds : Bounds) (bits : Nat)
    (wire : WireLiveClause) : Except String FCL := do
  let body ← wire.body.mapM (WireLiveLiteral.decode bounds bits)
  let head ← wire.head.mapM (WireLiveLiteral.decode bounds bits)
  if body.all (fun literal => match literal with | .P _ => true | _ => false) then
    if body.Nodup then
      if head.Nodup then return ⟨body, head⟩
      else throw "CB live clause head contains duplicates"
    else throw "CB live clause body contains duplicates"
  else throw "CB live context-clause body contains a non-predicate literal"

private def terminalOfGlobal (global : DecodedCBGlobalModelDocument) :=
  global.global.rsucc.succ.join3.hyper.literalOrder.termOrder.factorClosure.localResolution.terminal

private def liveTerminalMatches
    (terminal : ContextCalculus.CBTerminalStateWire.DecodedCBTerminalStateDocument)
    (index : Fin terminal.contexts.length) (wire : WireLiveContext) : Bool :=
  let state := terminal.contexts.get index
  decide (wire.todo_clause_ids.length = state.todo_count) &&
  decide (wire.dirty = state.dirty) &&
  decide (wire.pred_pool_ids.length = state.predPoolLen) &&
  decide (wire.pred_hwm = state.predHwm) &&
  decide (wire.succ_pool_ids.length = state.succPoolLen) &&
  decide (wire.succ_hwm = state.succHwm) &&
  decide (wire.rsucc_pool_ids.length = state.rsuccPoolLen) &&
  decide (wire.rsucc_hwm = state.rsuccHwm) &&
  decide (wire.rsucc_reach.length = state.rsuccReachLen) &&
  decide (wire.rsucc_offered = state.rsuccOffered) &&
  decide (wire.successor_reach_hwm = state.rsuccPairReachHwm) &&
  decide (wire.rsucc_edges_grew = state.rsuccEdgesGrew) &&
  decide (wire.predecessor_edge_seen = state.edgeSeen)

structure LiveIncomingEdge where
  predecessorIndex : Nat
  receiverIndex : Nat
  label : FTerm
  pushed : List FPred
deriving DecidableEq

structure LiveOutgoingEdge where
  label : FTerm
  targetIndex : Nat
deriving DecidableEq

private def ordinaryIncoming
    (send : ContextCalculus.CBPredSendCoverageWire.DecodedPredSendCoverageDocument) :
    List LiveIncomingEdge :=
  send.senders.flatMap fun sender => sender.edges.map fun edge =>
    { predecessorIndex := sender.senderIndex.val
      receiverIndex := edge.receiverIndex.val
      label := edge.label
      pushed := edge.pushed }

private def rootIncoming
    (send : ContextCalculus.CBPredSendCoverageWire.DecodedPredSendCoverageDocument) :
    List LiveIncomingEdge :=
  send.rootSender.toList.flatMap fun sender => sender.edges.map fun edge =>
    { predecessorIndex := sender.senderIndex.val
      receiverIndex := edge.receiverIndex.val
      label := .const edge.individual
      pushed := edge.pushed }

private def expectedIncoming
    (send : ContextCalculus.CBPredSendCoverageWire.DecodedPredSendCoverageDocument)
    (receiverIndex : Nat) : List LiveIncomingEdge :=
  (ordinaryIncoming send ++ rootIncoming send).filter
    fun edge => decide (edge.receiverIndex = receiverIndex)

private def expectedOutgoing
    (send : ContextCalculus.CBPredSendCoverageWire.DecodedPredSendCoverageDocument)
    (predecessorIndex : Nat) : List LiveOutgoingEdge :=
  (ordinaryIncoming send ++ rootIncoming send).filterMap fun edge =>
    if edge.predecessorIndex = predecessorIndex then
      some { label := edge.label, targetIndex := edge.receiverIndex }
    else none

structure DecodedLivePredecessorEdge where
  semantic : LiveIncomingEdge
  predPoolSeen : List Nat
  edgeSeen : Nat

def WireLivePredecessorEdge.decode (production : DecodedProductionRun)
    (bits receiverIndex : Nat) (wire : WireLivePredecessorEdge) :
    Except String DecodedLivePredecessorEdge := do
  if wire.predecessor_context < production.contexts.length then
    let pushed ← wire.pushed.mapM (WireLivePredicate.decode production.bounds bits)
    if pushed.Nodup then
      let label ← decodeRawTerm production.bounds bits wire.label
      return {
        semantic := {
          predecessorIndex := wire.predecessor_context
          receiverIndex := receiverIndex
          label := label
          pushed := pushed
        }
        predPoolSeen := wire.pred_pool_seen
        edgeSeen := wire.edge_seen
      }
    else throw "CB live predecessor pushed set contains duplicates"
  else throw "CB live predecessor context is outside the production run"

structure DecodedLiveSuccessorEdge where
  semantic : LiveOutgoingEdge
  reachHwm : Nat

def WireLiveSuccessorEdge.decode (production : DecodedProductionRun)
    (bits : Nat) (wire : WireLiveSuccessorEdge) : Except String DecodedLiveSuccessorEdge := do
  if wire.target_context < production.contexts.length then
    let label ← decodeRawTerm production.bounds bits wire.label
    return {
      semantic := {
        label := label
        targetIndex := wire.target_context
      }
      reachHwm := wire.rsucc_reach_hwm
    }
  else throw "CB live successor context is outside the production run"

structure DecodedLiveInsertionEvent (production : DecodedProductionRun)
    (ordinary root : List FCL) where
  sequence : Nat
  contextIndex : Fin production.contexts.length
  rootDomain : Bool
  root_eq : (production.contexts.get contextIndex).root = rootDomain
  clauseId : Nat
  clause : FCL

def WireLiveInsertionEvent.decode (production : DecodedProductionRun)
    (ordinary root : List FCL) (wire : WireLiveInsertionEvent) :
    Except String (DecodedLiveInsertionEvent production ordinary root) := do
  if hcontext : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length := ⟨wire.context_index, hcontext⟩
    let context := production.contexts.get contextIndex
    if hroot : context.root = wire.root then
      let arena := if wire.root then root else ordinary
      match arena[wire.clause_id]? with
      | some clause => return {
          sequence := wire.sequence
          contextIndex := contextIndex
          rootDomain := wire.root
          root_eq := hroot
          clauseId := wire.clause_id
          clause := clause
        }
      | none => throw "CB insertion-history clause id is outside its arena"
    else throw "CB insertion-history arena domain differs from its context"
  else throw "CB insertion-history context is outside the production run"

structure DecodedLiveContext
    (production : DecodedProductionRun)
    (terminal : ContextCalculus.CBTerminalStateWire.DecodedCBTerminalStateDocument)
    (ordinary root : List FCL) where
  contextIndex : Fin production.contexts.length
  contextId : Nat
  rootDomain : Bool
  context_id_eq : (production.contexts.get contextIndex).contextId = contextId
  root_eq : (production.contexts.get contextIndex).root = rootDomain
  retainedClauseIds : List Nat
  retained : List FCL
  retained_eq : retained = (production.contexts.get contextIndex).retained
  live : WireLiveContext
  predecessors : List DecodedLivePredecessorEdge
  predecessors_exact : predecessors.map (·.semantic) =
    expectedIncoming terminal.sendCoverage contextIndex.val
  successors : List DecodedLiveSuccessorEdge
  successors_exact : successors.map (·.semantic) =
    expectedOutgoing terminal.sendCoverage contextIndex.val
  predecessor_watermarks_exact : predecessors.map (·.edgeSeen) =
    live.predecessor_edge_seen
  successor_watermarks_exact : successors.map (·.reachHwm) =
    live.successor_reach_hwm
  terminalContextsEq : production.contexts.length = terminal.contexts.length
  terminal_matches : liveTerminalMatches terminal
    ⟨contextIndex.val, terminalContextsEq ▸ contextIndex.isLt⟩ live = true

private def insertionCovers
    {production : DecodedProductionRun} {ordinary root : List FCL}
    (history : List (DecodedLiveInsertionEvent production ordinary root))
    (contexts : List (DecodedLiveContext production terminal ordinary root)) : Bool :=
  contexts.all fun context => context.retainedClauseIds.all fun clauseId =>
    history.any fun event =>
      event.contextIndex.val == context.contextIndex.val && event.clauseId == clauseId

def WireLiveContext.decode (production : DecodedProductionRun)
    (terminal : ContextCalculus.CBTerminalStateWire.DecodedCBTerminalStateDocument)
    (bits : Nat) (ordinary root : List FCL) (wire : WireLiveContext) :
    Except String (DecodedLiveContext production terminal ordinary root) := do
  if hindex : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length := ⟨wire.context_index, hindex⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      if hroot : context.root = wire.root then
        let arena := if wire.root then root else ordinary
        let retained ← wire.retained_clause_ids.mapM fun clauseId =>
          match arena[clauseId]? with
          | some clause => pure clause
          | none => throw "CB live retained clause id is outside its arena"
        if hretained : retained = context.retained then
          let predecessors ← wire.predecessors.mapM
            (WireLivePredecessorEdge.decode production bits wire.context_index)
          let successors ← wire.successors.mapM
            (WireLiveSuccessorEdge.decode production bits)
          if hpredecessors : predecessors.map (·.semantic) =
              expectedIncoming terminal.sendCoverage wire.context_index then
          if hsuccessors : successors.map (·.semantic) =
              expectedOutgoing terminal.sendCoverage wire.context_index then
          if hpredWatermarks : predecessors.map (·.edgeSeen) = wire.predecessor_edge_seen then
          if hsuccWatermarks : successors.map (·.reachHwm) = wire.successor_reach_hwm then
          if hterminalLength : production.contexts.length = terminal.contexts.length then
            let terminalIndex : Fin terminal.contexts.length :=
              ⟨contextIndex.val, hterminalLength ▸ contextIndex.isLt⟩
            if hterminal : liveTerminalMatches terminal terminalIndex wire = true then
              return DecodedLiveContext.mk contextIndex wire.context_id wire.root
                hid hroot wire.retained_clause_ids retained hretained wire predecessors
                hpredecessors successors hsuccessors hpredWatermarks hsuccWatermarks
                hterminalLength hterminal
            else throw "CB live queues or high-water marks differ from terminal evidence"
          else throw "CB live and terminal-evidence context counts differ"
          else throw "CB live successor watermarks differ from successor records"
          else throw "CB live predecessor watermarks differ from predecessor records"
          else throw "CB live successors differ from certified outgoing edges"
          else throw "CB live predecessors differ from certified incoming edges"
        else throw "CB live retained clauses differ from the certified terminal context"
      else throw "CB live context uses the wrong clause-arena domain"
    else throw "CB live context id differs from the certified context"
  else throw "CB live context index is outside the certified production run"

structure DecodedLiveStateDocument where
  global : DecodedCBGlobalModelDocument
  compIndBits : Nat
  ordinaryArena : List FCL
  rootArena : List FCL
  insertionHistory : List (DecodedLiveInsertionEvent
    (rProduction global.global.rsucc) ordinaryArena rootArena)
  insertion_sequence_exact : insertionHistory.map (·.sequence) =
    List.range insertionHistory.length
  contexts : List (DecodedLiveContext (rProduction global.global.rsucc)
    (terminalOfGlobal global)
    ordinaryArena rootArena)
  context_indices_exact : contexts.map (fun context => context.contextIndex.val) =
    List.range (rProduction global.global.rsucc).contexts.length
  retained_insertions_present : insertionCovers insertionHistory contexts = true

structure WireProductionBoundGlobalModelDocument where
  version : Nat
  global_model : WireCBGlobalModelDocument
  live_state : WireLiveStateDocument
deriving FromJson, ToJson

def WireProductionBoundGlobalModelDocument.decode
    (wire : WireProductionBoundGlobalModelDocument) :
    Except String DecodedLiveStateDocument := do
  if wire.version != 1 then
    throw s!"unsupported production-bound CB global-model version {wire.version}"
  if wire.live_state.version != 2 then
    throw s!"unsupported CB live-state version {wire.live_state.version}"
  let global ← wire.global_model.decode
  let production := rProduction global.global.rsucc
  let terminal := terminalOfGlobal global
  if wire.live_state.rsucc_enabled = true then pure ()
    else throw "CB live state did not run with r-Succ enabled"
  if wire.live_state.reach_concept_ids = global.global.rsucc.reachConcepts then pure ()
    else throw "CB live reach table differs from r-Succ evidence"
  if wire.live_state.pending_messages = terminal.pendingMessages then pure ()
    else throw "CB live pending-message count differs from terminal evidence"
  if wire.live_state.message_truncated = terminal.messageTruncated then pure ()
    else throw "CB live message-truncation flag differs from terminal evidence"
  if _hnom : wire.live_state.nominal_truncated = terminal.nominalTruncated then
    let ordinary ← wire.live_state.ordinary_clause_arena.mapM
      (WireLiveClause.decode production.bounds wire.live_state.comp_ind_bits)
    let root ← wire.live_state.root_clause_arena.mapM
      (WireLiveClause.decode production.bounds wire.live_state.comp_ind_bits)
    let insertionHistory ← wire.live_state.insertion_history.mapM
      (WireLiveInsertionEvent.decode production ordinary root)
    if hinsertionSequence : insertionHistory.map (·.sequence) =
        List.range insertionHistory.length then
    let contexts ← wire.live_state.contexts.mapM
      (WireLiveContext.decode production terminal wire.live_state.comp_ind_bits ordinary root)
    let actual := contexts.map fun context => context.contextIndex.val
    let expected := List.range production.contexts.length
    if hcontexts : actual = expected then
    if hretainedInsertions : insertionCovers insertionHistory contexts = true then
      return {
        global := global
        compIndBits := wire.live_state.comp_ind_bits
        ordinaryArena := ordinary
        rootArena := root
        insertionHistory := insertionHistory
        insertion_sequence_exact := hinsertionSequence
        contexts := contexts
        context_indices_exact := hcontexts
        retained_insertions_present := hretainedInsertions
      }
    else throw "CB live retained clause has no chronological insertion event"
    else throw "CB live contexts do not exactly enumerate the certified contexts"
    else throw "CB insertion-history sequence is not exact"
  else throw "CB live Nom-truncation flag differs from terminal evidence"

def WireProductionBoundGlobalModelDocument.check
    (wire : WireProductionBoundGlobalModelDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireProductionBoundGlobalModelDocument.check_sound
    (wire : WireProductionBoundGlobalModelDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLiveStateDocument,
      wire.decode = .ok decoded ∧
      decoded.contexts.map (fun context => context.contextIndex.val) =
        List.range (rProduction decoded.global.global.rsucc).contexts.length ∧
      decoded.insertionHistory.map (·.sequence) =
        List.range decoded.insertionHistory.length ∧
      insertionCovers decoded.insertionHistory decoded.contexts = true ∧
      ∀ context ∈ decoded.contexts,
        context.retained =
          ((rProduction decoded.global.global.rsucc).contexts.get
            context.contextIndex).retained ∧
        context.predecessors.map (·.semantic) =
          expectedIncoming (terminalOfGlobal decoded.global).sendCoverage
            context.contextIndex.val ∧
        context.successors.map (·.semantic) =
          expectedOutgoing (terminalOfGlobal decoded.global).sendCoverage
            context.contextIndex.val := by
  cases hdecode : wire.decode with
  | error message => simp [WireProductionBoundGlobalModelDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, decoded.context_indices_exact,
        decoded.insertion_sequence_exact, decoded.retained_insertions_present,
        fun context _ => ⟨context.retained_eq, context.predecessors_exact,
          context.successors_exact⟩⟩

#print axioms WireProductionBoundGlobalModelDocument.check_sound

end ContextCalculus.CBLiveStateWire
