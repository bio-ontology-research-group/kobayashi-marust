import ContextCalculus.CBLiveInsertionDerivation

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

structure DecodedSourceSuccessorEdge (production : DecodedProductionRun) where
  targetIndex : Fin production.contexts.length
  label : FTerm

def decodeSourceSuccessorEdge (production : DecodedProductionRun)
    (bits : Nat) (wire : WireLiveSuccessorEdge) :
    Except String (DecodedSourceSuccessorEdge production) := do
  if hindex : wire.target_context < production.contexts.length then
    let targetIndex : Fin production.contexts.length :=
      ⟨wire.target_context, hindex⟩
    let label ← decodeRawTerm production.bounds bits wire.label
    return { targetIndex, label }
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
  predPoolIds : List Nat
  predHwm : Nat
  pred_hwm_eq : predHwm = predPoolIds.length
  predecessors : List (DecodedSourcePredecessorEdge production)
  pred_pool_seen_bounded : predecessors.all fun edge =>
    edge.predPoolSeen.all fun index => index < predPoolIds.length
  successors : List (DecodedSourceSuccessorEdge production)

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
                if hpredHwm : wire.pred_hwm = wire.pred_pool_ids.length then
                 let predecessors ← wire.predecessors.mapM
                   (decodeSourcePredecessorEdge production bits)
                 if hseenBounded : predecessors.all fun edge =>
                     edge.predPoolSeen.all fun index => index < wire.pred_pool_ids.length then
                  let successors ← wire.successors.mapM
                    (decodeSourceSuccessorEdge production bits)
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
                  predPoolIds := wire.pred_pool_ids
                  predHwm := wire.pred_hwm
                  pred_hwm_eq := hpredHwm
                  predecessors
                  pred_pool_seen_bounded := hseenBounded
                  successors
                  }
                 else throw "source-bound CB predecessor sent-pool index is outside the pool"
                else throw "source-bound CB Pred pool watermark is incomplete"
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
        }
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
