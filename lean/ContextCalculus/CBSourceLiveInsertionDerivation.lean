import ContextCalculus.CBLiveInsertionDerivation
import ContextCalculus.CBPredSendEnumeration

/-!
# Source-bound live CB insertion derivations

The legacy live document nests a complete global closure/model certificate.
Production can already construct the exact typed source and chronological
insertion history without that completeness object. This wire binds those two
native artifacts directly and proves the soundness half independently. Each
terminal retained clause is declared as an explicit local import, while the
chronological DAG, not that declaration, proves it context-valid.
-/

namespace ContextCalculus.CBSourceLiveInsertionDerivation

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBLiveStateWire
open ContextCalculus.CBLiveInsertionDerivation
open ContextCalculus.CBInterContextWire
open ContextCalculus.CBPredSendEnumeration

def predPoolCoversRetained (retainedClauseIds : List Nat)
    (retained : List FCL) (predPoolIds : List Nat) : Bool :=
  (retainedClauseIds.zip retained).all fun entry =>
    !predClauseEligible entry.2 || decide (entry.1 ∈ predPoolIds)

structure DecodedSourcePredecessorEdge (production : DecodedProductionRun) where
  predecessorIndex : Fin production.contexts.length
  label : FTerm
  pushed : List FPred
  pushed_nodup : pushed.Nodup
  predPoolSeen : List Nat
  pred_pool_seen_nodup : predPoolSeen.Nodup
  edgeSeen : Nat
  edge_seen_eq : edgeSeen = pushed.length

def decodeSourcePredecessorEdge (production : DecodedProductionRun)
    (bits : Nat) (wire : WireLivePredecessorEdge) :
    Except String (DecodedSourcePredecessorEdge production) := do
  if hindex : wire.predecessor_context < production.contexts.length then
    let predecessorIndex : Fin production.contexts.length :=
      ⟨wire.predecessor_context, hindex⟩
    let label ← decodeRawTerm production.bounds bits wire.label
    let pushed ← wire.pushed.mapM
      (WireLivePredicate.decode production.bounds bits)
    if hpushed : pushed.Nodup then
      if hseen : wire.pred_pool_seen.Nodup then
        if hedgeSeen : wire.edge_seen = pushed.length then
          return {
            predecessorIndex, label, pushed
            pushed_nodup := hpushed
            predPoolSeen := wire.pred_pool_seen
            pred_pool_seen_nodup := hseen
            edgeSeen := wire.edge_seen
            edge_seen_eq := hedgeSeen }
        else throw "source-bound CB predecessor edge watermark is incomplete"
      else throw "source-bound CB predecessor sent-pool list contains a duplicate"
    else throw "source-bound CB predecessor pushed set contains a duplicate"
  else throw "source-bound CB predecessor edge has an invalid context"

structure DecodedSourceSuccessorEdge (production : DecodedProductionRun)
    (reachLength : Nat) where
  targetIndex : Fin production.contexts.length
  label : FTerm
  reachHwm : Nat
  reach_hwm_eq : reachHwm = reachLength

def decodeSourceSuccessorEdge (production : DecodedProductionRun)
    (bits reachLength : Nat) (wire : WireLiveSuccessorEdge) :
    Except String (DecodedSourceSuccessorEdge production reachLength) := do
  if hindex : wire.target_context < production.contexts.length then
    let targetIndex : Fin production.contexts.length :=
      ⟨wire.target_context, hindex⟩
    let label ← decodeRawTerm production.bounds bits wire.label
    if hhwm : wire.rsucc_reach_hwm = reachLength then
      return {
        targetIndex
        label
        reachHwm := wire.rsucc_reach_hwm
        reach_hwm_eq := hhwm }
    else throw "source-bound CB successor r-Succ watermark is incomplete"
  else throw "source-bound CB successor edge has an invalid context"

structure DecodedSourceLiveContext
    (production : DecodedProductionRun) (ordinary root : List FCL) where
  contextIndex : Fin production.contexts.length
  contextId : Nat
  rootDomain : Bool
  context_id_eq : (production.contexts.get contextIndex).contextId = contextId
  root_eq : (production.contexts.get contextIndex).root = rootDomain
  retainedClauseIds : List Nat
  retained_clause_ids_nodup : retainedClauseIds.Nodup
  retained : List FCL
  retained_eq : retained = (production.contexts.get contextIndex).retained
  wireTodoCount : Nat
  wireDirty : Bool
  todo_empty : wireTodoCount = 0
  clean : wireDirty = false
  predPoolIds : List Nat
  pred_pool_ids_nodup : predPoolIds.Nodup
  pred_pool_ids_bounded : predPoolIds.all fun clauseId =>
    clauseId < (if rootDomain then root else ordinary).length
  pred_pool_covers_retained :
    predPoolCoversRetained retainedClauseIds retained predPoolIds = true
  predHwm : Nat
  pred_hwm_eq : predHwm = predPoolIds.length
  succPoolIds : List Nat
  succHwm : Nat
  succ_hwm_eq : succHwm = succPoolIds.length
  rSuccPoolIds : List Nat
  rSuccHwm : Nat
  rsucc_hwm_eq : rSuccHwm = rSuccPoolIds.length
  rSuccReach : List FPred
  rSuccOffered : Nat
  wireRSuccEdgesGrew : Bool
  rsucc_offered_eq : rSuccOffered = rSuccReach.length
  rsucc_edges_clean : wireRSuccEdgesGrew = false
  predecessors : List (DecodedSourcePredecessorEdge production)
  pred_pool_seen_bounded : predecessors.all fun edge =>
    edge.predPoolSeen.all fun index => index < predPoolIds.length
  successors : List (DecodedSourceSuccessorEdge production rSuccReach.length)

def decodeSourceLiveContext (production : DecodedProductionRun)
    (bits : Nat) (ordinary root : List FCL) (wire : WireLiveContext) :
    Except String (DecodedSourceLiveContext production ordinary root) := do
  if hindex : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length :=
      ⟨wire.context_index, hindex⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      if hroot : context.root = wire.root then
        if _hnominal : context.nominalGround = wire.nominal_ground then
          if _hquery : context.queryConcept = wire.query_concept then
            let core ← wire.core.mapM (WireLivePredicate.decode production.bounds bits)
            if _hcore : core = context.core then
              let arena := if wire.root then root else ordinary
              let retained ← wire.retained_clause_ids.mapM fun clauseId =>
                match arena[clauseId]? with
                | some clause => pure clause
                | none => throw "source-bound CB retained clause id is outside its arena"
              if hretainedIds : wire.retained_clause_ids.Nodup then
                if hretained : retained = context.retained then
                  if htodo : wire.todo_clause_ids.length = 0 then
                    if hclean : wire.dirty = false then
                      if hpredNodup : wire.pred_pool_ids.Nodup then
                        if hpredBounded : wire.pred_pool_ids.all fun clauseId =>
                            clauseId < arena.length then
                          if hpredCoverage : predPoolCoversRetained
                              wire.retained_clause_ids retained wire.pred_pool_ids = true then
                            if hpredHwm : wire.pred_hwm = wire.pred_pool_ids.length then
                              if hsuccHwm : wire.succ_hwm = wire.succ_pool_ids.length then
                                if hrsuccHwm : wire.rsucc_hwm = wire.rsucc_pool_ids.length then
                                  let rSuccReach ← wire.rsucc_reach.mapM
                                    (WireLivePredicate.decode production.bounds bits)
                                  if hrsuccOffered : wire.rsucc_offered = rSuccReach.length then
                                    if hrsuccClean : wire.rsucc_edges_grew = false then
                                      let predecessors ← wire.predecessors.mapM
                                        (decodeSourcePredecessorEdge production bits)
                                      if hseenBounded : predecessors.all fun edge =>
                                          edge.predPoolSeen.all fun index =>
                                            index < wire.pred_pool_ids.length then
                                        let successors ← wire.successors.mapM
                                          (decodeSourceSuccessorEdge production bits
                                            rSuccReach.length)
                                        return {
                                          contextIndex
                                          contextId := wire.context_id
                                          rootDomain := wire.root
                                          context_id_eq := hid
                                          root_eq := hroot
                                          retainedClauseIds := wire.retained_clause_ids
                                          retained_clause_ids_nodup := hretainedIds
                                          retained
                                          retained_eq := hretained
                                          wireTodoCount := wire.todo_clause_ids.length
                                          wireDirty := wire.dirty
                                          todo_empty := htodo
                                          clean := hclean
                                          predPoolIds := wire.pred_pool_ids
                                          pred_pool_ids_nodup := hpredNodup
                                          pred_pool_ids_bounded := hpredBounded
                                          pred_pool_covers_retained := hpredCoverage
                                          predHwm := wire.pred_hwm
                                          pred_hwm_eq := hpredHwm
                                          succPoolIds := wire.succ_pool_ids
                                          succHwm := wire.succ_hwm
                                          succ_hwm_eq := hsuccHwm
                                          rSuccPoolIds := wire.rsucc_pool_ids
                                          rSuccHwm := wire.rsucc_hwm
                                          rsucc_hwm_eq := hrsuccHwm
                                          rSuccReach
                                          rSuccOffered := wire.rsucc_offered
                                          wireRSuccEdgesGrew := wire.rsucc_edges_grew
                                          rsucc_offered_eq := hrsuccOffered
                                          rsucc_edges_clean := hrsuccClean
                                          predecessors
                                          pred_pool_seen_bounded := hseenBounded
                                          successors
                                        }
                                      else
                                        throw "source-bound CB predecessor sent-pool index is outside the pool"
                                    else throw "source-bound CB context still has dirty r-Succ edges"
                                  else throw "source-bound CB r-Succ offers are incomplete"
                                else throw "source-bound CB r-Succ pool watermark is incomplete"
                              else throw "source-bound CB Succ pool watermark is incomplete"
                            else throw "source-bound CB Pred pool watermark is incomplete"
                          else throw "source-bound CB Pred pool omits an eligible retained clause"
                        else throw "source-bound CB Pred pool clause id is outside its arena"
                      else throw "source-bound CB Pred pool contains a duplicate clause id"
                    else throw "source-bound CB context remains dirty"
                  else throw "source-bound CB context has pending clauses"
                else throw "source-bound CB retained clauses differ from production"
              else throw "source-bound CB retained clause ids contain a duplicate"
            else throw "source-bound CB context core differs from production"
          else throw "source-bound CB query concept differs from production"
        else throw "source-bound CB nominal-ground marker differs from production"
      else throw "source-bound CB context uses the wrong arena domain"
    else throw "source-bound CB context id differs from production"
  else throw "source-bound CB context index is outside production"

def sourceInsertionCovers
    {production : DecodedProductionRun} {ordinary root : List FCL}
    (history : List (DecodedLiveInsertionEvent production ordinary root))
    (contexts : List (DecodedSourceLiveContext production ordinary root)) : Bool :=
  contexts.all fun context => context.retained.all fun clause =>
    history.any fun event =>
      decide (event.contextIndex = context.contextIndex) &&
        decide (event.clause = clause)

structure WireSourceLiveInsertionDerivationDocument where
  version : Nat
  production : WireProductionRun
  comp_ind_bits : Nat
  ordinary_clause_arena : List WireLiveClause
  root_clause_arena : List WireLiveClause
  insertion_history : List WireLiveInsertionEvent
  contexts : List WireLiveContext
  insertion_evidence : List WireEventEvidence
  pending_messages : Nat
  message_truncated : Bool
  nominal_truncated : Bool
deriving FromJson, ToJson

structure DecodedSourceLiveInsertionDerivationDocument where
  production : DecodedProductionRun
  compIndBits : Nat
  ordinaryArena : List FCL
  rootArena : List FCL
  insertionHistory : List
    (DecodedLiveInsertionEvent production ordinaryArena rootArena)
  insertion_sequence_exact : insertionHistory.map (·.sequence) =
    List.range insertionHistory.length
  contexts : List
    (DecodedSourceLiveContext production ordinaryArena rootArena)
  context_indices_exact : contexts.map (fun context => context.contextIndex.val) =
    List.range production.contexts.length
  retained_insertions_present :
    sourceInsertionCovers insertionHistory contexts = true
  history : DecodedCertifiedHistory production ordinaryArena rootArena insertionHistory
  wirePendingMessages : Nat
  wireMessageTruncated : Bool
  wireNominalTruncated : Bool
  messages_empty : wirePendingMessages = 0
  message_complete : wireMessageTruncated = false
  nominal_complete : wireNominalTruncated = false

def WireSourceLiveInsertionDerivationDocument.decode
    (wire : WireSourceLiveInsertionDerivationDocument) :
    Except String DecodedSourceLiveInsertionDerivationDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB live-derivation version {wire.version}"
  let production ← wire.production.decode
  let ordinary ← wire.ordinary_clause_arena.mapM
    (WireLiveClause.decode production.bounds wire.comp_ind_bits)
  let root ← wire.root_clause_arena.mapM
    (WireLiveClause.decode production.bounds wire.comp_ind_bits)
  let insertionHistory ← wire.insertion_history.mapM
    (WireLiveInsertionEvent.decode production wire.comp_ind_bits ordinary root)
  if hsequence : insertionHistory.map (·.sequence) =
      List.range insertionHistory.length then
    let contexts ← wire.contexts.mapM
      (decodeSourceLiveContext production wire.comp_ind_bits ordinary root)
    if hcontexts : contexts.map (fun context => context.contextIndex.val) =
        List.range production.contexts.length then
      if hcoverage : sourceInsertionCovers insertionHistory contexts = true then
        let history ← decodeHistoryEvidence production ordinary root insertionHistory
          wire.insertion_evidence
        if hpending : wire.pending_messages = 0 then
          if hmessages : wire.message_truncated = false then
            if hnominal : wire.nominal_truncated = false then
              return {
                production
                compIndBits := wire.comp_ind_bits
                ordinaryArena := ordinary
                rootArena := root
                insertionHistory
                insertion_sequence_exact := hsequence
                contexts
                context_indices_exact := hcontexts
                retained_insertions_present := hcoverage
                history
                wirePendingMessages := wire.pending_messages
                wireMessageTruncated := wire.message_truncated
                wireNominalTruncated := wire.nominal_truncated
                messages_empty := hpending
                message_complete := hmessages
                nominal_complete := hnominal
              }
            else throw "source-bound CB nominal generation was truncated"
          else throw "source-bound CB message processing was truncated"
        else throw "source-bound CB terminal state has pending messages"
      else throw "source-bound CB insertion history omits a retained clause"
    else throw "source-bound CB live contexts are incomplete or reordered"
  else throw "source-bound CB insertion sequence is incomplete or reordered"

def WireSourceLiveInsertionDerivationDocument.check
    (wire : WireSourceLiveInsertionDerivationDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedSourceLiveInsertionDerivationDocument.retained_has_event
    (decoded : DecodedSourceLiveInsertionDerivationDocument)
    (context : DecodedSourceLiveContext decoded.production
      decoded.ordinaryArena decoded.rootArena)
    (hcontext : context ∈ decoded.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained) :
    ∃ event ∈ decoded.insertionHistory,
      event.contextIndex = context.contextIndex ∧ event.clause = clause := by
  have hcoverage := decoded.retained_insertions_present
  simp only [sourceInsertionCovers, List.all_eq_true] at hcoverage
  have hcontextCoverage := hcoverage context hcontext
  have hclauseCoverage := hcontextCoverage clause hclause
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hclauseCoverage
  exact hclauseCoverage

theorem DecodedSourceLiveInsertionDerivationDocument.terminal_global
    (decoded : DecodedSourceLiveInsertionDerivationDocument) :
    decoded.wirePendingMessages = 0 ∧
      decoded.wireMessageTruncated = false ∧
      decoded.wireNominalTruncated = false :=
  ⟨decoded.messages_empty, decoded.message_complete, decoded.nominal_complete⟩

theorem DecodedSourceLiveInsertionDerivationDocument.terminal_context
    (decoded : DecodedSourceLiveInsertionDerivationDocument)
    (context : DecodedSourceLiveContext decoded.production
      decoded.ordinaryArena decoded.rootArena)
    (_hcontext : context ∈ decoded.contexts) :
    context.wireTodoCount = 0 ∧ context.wireDirty = false ∧
      context.predHwm = context.predPoolIds.length ∧
      context.succHwm = context.succPoolIds.length ∧
      context.rSuccHwm = context.rSuccPoolIds.length ∧
      context.rSuccOffered = context.rSuccReach.length ∧
      context.wireRSuccEdgesGrew = false ∧
      ∀ edge ∈ context.successors,
        edge.reachHwm = context.rSuccReach.length := by
  refine ⟨context.todo_empty, context.clean, context.pred_hwm_eq,
    context.succ_hwm_eq, context.rsucc_hwm_eq, context.rsucc_offered_eq,
    context.rsucc_edges_clean, ?_⟩
  intro edge _hedge
  exact edge.reach_hwm_eq

theorem DecodedSourceLiveInsertionDerivationDocument.pred_pool_contains_eligible_retained
    (decoded : DecodedSourceLiveInsertionDerivationDocument)
    (context : DecodedSourceLiveContext decoded.production
      decoded.ordinaryArena decoded.rootArena)
    (_hcontext : context ∈ decoded.contexts)
    (entry : Nat × FCL)
    (hentry : entry ∈ context.retainedClauseIds.zip context.retained)
    (heligible : predClauseEligible entry.2 = true) :
    entry.1 ∈ context.predPoolIds := by
  have hcovered := List.all_eq_true.mp context.pred_pool_covers_retained entry hentry
  simp only [heligible, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hcovered
  exact hcovered

theorem DecodedSourceLiveInsertionDerivationDocument.retained_contextValid
    (decoded : DecodedSourceLiveInsertionDerivationDocument)
    (context : DecodedSourceLiveContext decoded.production
      decoded.ordinaryArena decoded.rootArena)
    (hcontext : context ∈ decoded.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    {D : Type} (model : TModel D)
    (hontology : ∀ source ∈ decoded.production.source.ontology,
      valid model source) :
    CBInterContext.ContextValid model
      (decoded.production.contexts.get context.contextIndex).core clause := by
  obtain ⟨event, hevent, hindex, hclauseEq⟩ :=
    decoded.retained_has_event context hcontext clause hclause
  intro assignment hcore
  rw [← hclauseEq]
  exact decoded.history.sound event hevent model assignment hontology (by
    rw [hindex]
    exact hcore)

theorem DecodedSourceLiveInsertionDerivationDocument.production_retained_valid
    (decoded : DecodedSourceLiveInsertionDerivationDocument)
    {D : Type} (model : TModel D)
    (hontology : ∀ source ∈ decoded.production.source.ontology,
      valid model source) :
    ProductionRetainedValid decoded.production model := by
  intro index clause hclause
  have hindex : index.val ∈ List.range decoded.production.contexts.length :=
    List.mem_range.mpr index.isLt
  rw [← decoded.context_indices_exact] at hindex
  rcases List.mem_map.mp hindex with ⟨context, hcontext, hcontextIndex⟩
  have heq : context.contextIndex = index := Fin.ext hcontextIndex
  subst index
  apply decoded.retained_contextValid context hcontext clause
  · rw [context.retained_eq]
    exact hclause
  · exact hontology

theorem WireSourceLiveInsertionDerivationDocument.check_sound
    (wire : WireSourceLiveInsertionDerivationDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceLiveInsertionDerivationDocument,
      wire.decode = .ok decoded ∧
      ∀ (D : Type) (model : TModel D),
        (∀ source ∈ decoded.production.source.ontology,
          valid model source) →
        ProductionRetainedValid decoded.production model := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireSourceLiveInsertionDerivationDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl, fun D model hontology =>
        decoded.production_retained_valid model hontology⟩

#print axioms DecodedSourceLiveInsertionDerivationDocument.retained_contextValid
#print axioms DecodedSourceLiveInsertionDerivationDocument.production_retained_valid
#print axioms WireSourceLiveInsertionDerivationDocument.check_sound

end ContextCalculus.CBSourceLiveInsertionDerivation
