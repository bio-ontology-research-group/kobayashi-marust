import ContextCalculus.CBLiveStateWire

/-!
# Chronological soundness of live CB insertions

The live engine records every successful context-clause insertion in one global
chronological stream. A local derivation may use only explicitly selected,
earlier events from the same context. It may then append an arbitrary checked
`CBProductionTrace` fragment, allowing source instantiation and intermediate
resolution clauses that were not themselves retained by KM. This module proves
the induction principle consumed by the production evidence wire.

Inter-context arrivals require the separate checked Pred/r-Pred transfer
constructor and are deliberately not admitted as local derivations here.
-/

namespace ContextCalculus.CBLiveInsertionDerivation

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBLiveStateWire
open ContextCalculus.CBGlobalClosureWire

abbrev LiveEvent (production : DecodedProductionRun)
    (ordinary root : List FCL) :=
  DecodedLiveInsertionEvent production ordinary root

def EventSound (event : LiveEvent production ordinary root) : Prop :=
  ∀ {D : Type} (model : TModel D) (assignment : Int → D),
    (∀ source ∈ production.source.ontology, valid model source) →
    CoreHolds model assignment
      (production.contexts.get event.contextIndex).core →
    HoldsAt model assignment event.clause

structure PriorLocalRef
    (done : List (LiveEvent production ordinary root))
    (event : LiveEvent production ordinary root) where
  index : Fin done.length
  context_eq : (done.get index).contextIndex = event.contextIndex

def priorClauses
    {done : List (LiveEvent production ordinary root)}
    {event : LiveEvent production ordinary root}
    (references : List (PriorLocalRef done event)) : List FCL :=
  references.map fun reference => (done.get reference.index).clause

inductive EventEvidence
    (done : List (LiveEvent production ordinary root)) :
    LiveEvent production ordinary root → Type
  | seed (event) (hseed : event.origin ≠ .derived) : EventEvidence done event
  | localTrace (event)
      (references : List (PriorLocalRef done event))
      (trace : List Entry) (final : List FCL)
      (checked : checkFold production.source.ontology
        (production.contexts.get event.contextIndex).assumptions
        (priorClauses references) trace = some final)
      (conclusion : event.clause ∈ final) : EventEvidence done event
  | pred (event) (predEvidence : DecodedLivePredEvidence production)
      (event_evidence_eq : event.predEvidence = some predEvidence)
      (result_eq : predEvidence.result = event.clause)
      (senderIndex : Fin done.length)
      (sender_context_eq : (done.get senderIndex).contextIndex = predEvidence.senderIndex)
      (sender_clause_eq : (done.get senderIndex).clause = predEvidence.senderClause)
      (providerIndices : List (Fin done.length))
      (provider_contexts_eq : providerIndices.all fun index =>
        decide ((done.get index).contextIndex = event.contextIndex))
      (provider_clauses_eq : providerIndices.map (fun index => (done.get index).clause) =
        predEvidence.providers.map (·.clause)) : EventEvidence done event
  | discarded (event)
      (trace : List Entry) (final : List FCL)
      (checked : checkFold production.source.ontology
        (production.contexts.get event.contextIndex).assumptions [] trace = some final)
      (strengtheningIndex : Fin final.length)
      (strengthens : Strengthens (final.get strengtheningIndex) event.clause) :
      EventEvidence done event

inductive CertifiedHistory :
    List (LiveEvent production ordinary root) → Type
  | nil : CertifiedHistory []
  | snoc {done event} : CertifiedHistory done → EventEvidence done event →
      CertifiedHistory (done ++ [event])

private theorem prior_local_sound
    {done : List (LiveEvent production ordinary root)}
    {event : LiveEvent production ordinary root}
    (hall : ∀ prior ∈ done, EventSound prior)
    (references : List (PriorLocalRef done event))
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ production.source.ontology, valid model source)
    (hcore : CoreHolds model assignment
      (production.contexts.get event.contextIndex).core) :
    ∀ clause ∈ priorClauses references, HoldsAt model assignment clause := by
  intro clause hclause
  simp only [priorClauses, List.mem_map] at hclause
  obtain ⟨reference, _, rfl⟩ := hclause
  have hprior : EventSound (done.get reference.index) :=
    hall (done.get reference.index) (List.get_mem done reference.index)
  have hpriorCore : CoreHolds model assignment
      (production.contexts.get (done.get reference.index).contextIndex).core := by
    rw [congrArg (fun contextIndex =>
      (production.contexts.get contextIndex).core) reference.context_eq]
    exact hcore
  exact hprior model assignment hontology hpriorCore

theorem EventEvidence.sound
    {done : List (LiveEvent production ordinary root)}
    {event : LiveEvent production ordinary root}
    (evidence : EventEvidence done event)
    (hall : ∀ prior ∈ done, EventSound prior) : EventSound event := by
  cases evidence with
  | seed hseed =>
      intro D model assignment hontology hcore
      exact event.seed_sound model assignment hontology hcore hseed
  | localTrace references trace final checked conclusion =>
      intro D model assignment hontology hcore
      have hfinal := checkFold_sound model assignment hontology
        (fun assumption hassumption => by
          rw [(production.contexts.get event.contextIndex).assumptions_eq]
            at hassumption
          simp only [List.mem_map] at hassumption
          obtain ⟨predicate, hpredicate, rfl⟩ := hassumption
          intro _
          exact ⟨.P predicate, List.mem_singleton.mpr rfl,
            hcore predicate hpredicate⟩)
        (prior_local_sound hall references model assignment hontology hcore)
        checked
      exact hfinal event.clause conclusion
  | pred predEvidence _ result_eq senderIndex senderContext senderClause
      providerIndices providerContexts providerClauses =>
      intro D model assignment hontology hcore
      have hsenderEvent : EventSound (done.get senderIndex) :=
        hall (done.get senderIndex) (List.get_mem done senderIndex)
      have hsender : CBInterContext.ContextValid model
          (production.contexts.get predEvidence.senderIndex).core
          predEvidence.senderClause := by
        intro senderAssignment senderCore
        rw [← senderClause]
        exact hsenderEvent model senderAssignment hontology (by
          rw [senderContext]
          exact senderCore)
      have hproviders : ∀ provider ∈ predEvidence.providers,
          CBInterContext.ContextValid model
            (production.contexts.get event.contextIndex).core provider.clause := by
        intro provider hprovider
        have hclause : provider.clause ∈
            providerIndices.map (fun index => (done.get index).clause) := by
          rw [providerClauses]
          exact List.mem_map.mpr ⟨provider, hprovider, rfl⟩
        obtain ⟨index, hindex, hclauseEq⟩ := List.mem_map.mp hclause
        have hcontext : (done.get index).contextIndex = event.contextIndex := by
          have hallContexts := List.all_eq_true.mp providerContexts index hindex
          exact of_decide_eq_true hallContexts
        have hproviderEvent : EventSound (done.get index) :=
          hall (done.get index) (List.get_mem done index)
        intro providerAssignment providerCore
        rw [← hclauseEq]
        exact hproviderEvent model providerAssignment hontology (by
          rw [hcontext]
          exact providerCore)
      have hresult := predEvidence.result_contextValid
        (production.contexts.get event.contextIndex).core model hsender hproviders
      rw [← result_eq]
      exact hresult assignment hcore
  | discarded trace final checked strengtheningIndex strengthens =>
      intro D model assignment hontology hcore
      apply HoldsAt.of_strengthens model assignment strengthens
      have hfinal := checkFold_sound model assignment hontology
        (fun assumption hassumption => by
          rw [(production.contexts.get event.contextIndex).assumptions_eq]
            at hassumption
          simp only [List.mem_map] at hassumption
          obtain ⟨predicate, hpredicate, rfl⟩ := hassumption
          intro _
          exact ⟨.P predicate, List.mem_singleton.mpr rfl,
            hcore predicate hpredicate⟩)
        (by simp) checked
      exact hfinal (final.get strengtheningIndex)
        (List.get_mem final strengtheningIndex)

theorem CertifiedHistory.sound
    {history : List (LiveEvent production ordinary root)}
    (certificate : CertifiedHistory history) :
    ∀ event ∈ history, EventSound event := by
  induction certificate
  case nil => simp
  case snoc =>
      rename_i priorCertificate evidence ih
      intro candidate hcandidate
      simp only [List.mem_append, List.mem_singleton] at hcandidate
      rcases hcandidate with hprior | rfl
      · exact ih candidate hprior
      · exact evidence.sound ih

structure WirePriorLocalRef where
  event_index : Nat
deriving FromJson, ToJson

structure WireEventEvidence where
  kind : String
  prior_events : List WirePriorLocalRef
  trace : List WireProductionEntry
  discarded : List WireDiscardedClause
  sender_event : Option WirePriorLocalRef
  provider_events : Option (List WirePriorLocalRef)
deriving FromJson, ToJson

def WirePriorLocalRef.decode
    (done : List (LiveEvent production ordinary root))
    (event : LiveEvent production ordinary root)
    (wire : WirePriorLocalRef) : Except String (PriorLocalRef done event) := do
  if hindex : wire.event_index < done.length then
    let index : Fin done.length := ⟨wire.event_index, hindex⟩
    if hcontext : (done.get index).contextIndex = event.contextIndex then
      return { index, context_eq := hcontext }
    else throw "CB local insertion derivation cites another context"
  else throw "CB local insertion derivation cites a non-earlier event"

def WireEventEvidence.decode
    (production : DecodedProductionRun)
    (done : List (LiveEvent production ordinary root))
    (event : LiveEvent production ordinary root)
    (wire : WireEventEvidence) : Except String (EventEvidence done event) := do
  match wire.kind with
  | "seed" =>
      if wire.prior_events.isEmpty ∧ wire.trace.isEmpty ∧ wire.discarded.isEmpty ∧
          wire.sender_event.isNone ∧ wire.provider_events.isNone then
        if hseed : event.origin ≠ .derived then
          return .seed event hseed
        else throw "CB derived insertion is labelled as a seed"
      else throw "CB insertion seed unexpectedly carries derivation data"
  | "local" =>
      if _horigin : event.origin = .derived then
        if !wire.discarded.isEmpty ∨ wire.sender_event.isSome ∨
            wire.provider_events.isSome then
          throw "CB local insertion trace unexpectedly carries discarded witnesses"
        let references ← wire.prior_events.mapM
          (WirePriorLocalRef.decode done event)
        let trace ← wire.trace.mapM
          (WireProductionEntry.decode production.bounds)
        match hchecked : checkFold production.source.ontology
            (production.contexts.get event.contextIndex).assumptions
            (priorClauses references) trace with
        | none => throw "CB local insertion trace was rejected"
        | some final =>
            if hconclusion : event.clause ∈ final then
              return .localTrace event references trace final hchecked hconclusion
            else throw "CB local insertion trace does not derive its event clause"
      else throw "CB insertion seed is labelled as a local derivation"
  | "discarded" =>
      if _horigin : event.origin = .derived then
        if !wire.prior_events.isEmpty ∨ wire.sender_event.isSome ∨
            wire.provider_events.isSome then
          throw "CB discarded insertion evidence unexpectedly cites earlier events"
        let trace ← wire.trace.mapM
          (WireProductionEntry.decode production.bounds)
        match hchecked : checkFold production.source.ontology
            (production.contexts.get event.contextIndex).assumptions [] trace with
        | none => throw "CB discarded insertion trace was rejected"
        | some final =>
            let discarded ← wire.discarded.mapM
              (WireDiscardedClause.decode production.bounds final)
            let isTarget := fun (witness : DecodedDiscardedClause final) =>
              decide (witness.clause = event.clause)
            match hfound : discarded.find? isTarget with
            | none => throw "CB discarded evidence omits the exact live event clause"
            | some witness =>
                have hclause : witness.clause = event.clause :=
                  of_decide_eq_true (by
                    simpa [isTarget] using List.find?_some hfound)
                return .discarded event trace final hchecked
                  witness.strengtheningIndex (hclause ▸ witness.strengthens)
      else throw "CB insertion seed is labelled as discarded"
  | "pred" =>
      if _horigin : event.origin = .derived then
        if !wire.prior_events.isEmpty ∨ !wire.trace.isEmpty ∨
            !wire.discarded.isEmpty then
          throw "CB Pred insertion unexpectedly carries local trace data"
        match hevidence : event.predEvidence with
        | none => throw "CB Pred insertion has no checked live Pred evidence"
        | some predEvidence =>
          let senderWire ← match wire.sender_event with
            | some reference => pure reference
            | none => throw "CB Pred insertion omits its sender event"
          if hsenderIndex : senderWire.event_index < done.length then
            let senderIndex : Fin done.length :=
              ⟨senderWire.event_index, hsenderIndex⟩
            if hsenderContext :
                (done.get senderIndex).contextIndex = predEvidence.senderIndex then
              if hsenderClause :
                  (done.get senderIndex).clause = predEvidence.senderClause then
                let providerWires ← match wire.provider_events with
                  | some references => pure references
                  | none => throw "CB Pred insertion omits its provider events"
                let providerIndices ← providerWires.mapM fun reference =>
                  if hindex : reference.event_index < done.length then
                    pure (⟨reference.event_index, hindex⟩ : Fin done.length)
                  else throw "CB Pred provider cites a non-earlier event"
                if hcontexts : providerIndices.all fun index =>
                    decide ((done.get index).contextIndex = event.contextIndex) then
                  let actualClauses := providerIndices.map fun index =>
                    (done.get index).clause
                  let expectedClauses := predEvidence.providers.map (·.clause)
                  if hclauses : actualClauses = expectedClauses then
                    if hresult : predEvidence.result = event.clause then
                      return .pred event predEvidence hevidence hresult senderIndex
                        hsenderContext hsenderClause providerIndices hcontexts hclauses
                    else throw "CB Pred evidence result differs from its live event"
                  else throw "CB Pred provider events differ from checked provider clauses"
                else throw "CB Pred provider event belongs to another receiver context"
              else throw "CB Pred sender event clause differs from its checked sender clause"
            else throw "CB Pred sender event belongs to another context"
          else throw "CB Pred sender cites a non-earlier event"
      else throw "CB insertion seed is labelled as Pred-derived"
  | kind => throw s!"unsupported CB insertion evidence kind {kind}"

structure DecodedHistoryPrefix
    (production : DecodedProductionRun) (ordinary root : List FCL) where
  history : List (LiveEvent production ordinary root)
  certificate : CertifiedHistory history

structure DecodedHistoryResult
    (production : DecodedProductionRun) (ordinary root : List FCL)
    (initial remaining : List (LiveEvent production ordinary root)) where
  history : List (LiveEvent production ordinary root)
  history_eq : history = initial ++ remaining
  certificate : CertifiedHistory history

def decodeHistoryLoop (production : DecodedProductionRun) :
    (ordinary root : List FCL) →
    (accumulated : DecodedHistoryPrefix production ordinary root) →
    (remaining : List (LiveEvent production ordinary root)) →
    List WireEventEvidence →
    Except String (DecodedHistoryResult production ordinary root
      accumulated.history remaining)
  | ordinary, root, accumulated, [], [] =>
      pure {
        history := accumulated.history
        history_eq := by simp
        certificate := accumulated.certificate
      }
  | ordinary, root, accumulated, event :: remaining, wire :: wires => do
      let evidence ← wire.decode production accumulated.history event
      let next : DecodedHistoryPrefix production ordinary root := {
        history := accumulated.history ++ [event]
        certificate := accumulated.certificate.snoc evidence
      }
      let decoded ← decodeHistoryLoop production ordinary root next remaining wires
      return {
        history := decoded.history
        history_eq := by
          simpa [next, List.append_assoc] using decoded.history_eq
        certificate := decoded.certificate
      }
  | _, _, _, _, _ => throw "CB insertion evidence does not match history length"
termination_by _ _ _ remaining _ => remaining.length

structure DecodedCertifiedHistory
    (production : DecodedProductionRun) (ordinary root : List FCL)
    (history : List (LiveEvent production ordinary root)) where
  certificate : CertifiedHistory history

def decodeHistoryEvidence (production : DecodedProductionRun)
    (ordinary root : List FCL)
    (history : List (LiveEvent production ordinary root))
    (wire : List WireEventEvidence) :
    Except String (DecodedCertifiedHistory production ordinary root history) := do
  let decoded ← decodeHistoryLoop production ordinary root
    { history := [], certificate := .nil } history wire
  have hexact : decoded.history = history := by
    simpa using decoded.history_eq
  return { certificate := hexact ▸ decoded.certificate }

theorem DecodedCertifiedHistory.sound
    (decoded : DecodedCertifiedHistory production ordinary root history) :
    ∀ event ∈ history, EventSound event :=
  decoded.certificate.sound

structure WireLiveInsertionDerivationDocument where
  version : Nat
  production_bound : WireProductionBoundGlobalModelDocument
  insertion_evidence : List WireEventEvidence
deriving FromJson, ToJson

structure DecodedLiveInsertionDerivationDocument where
  live : DecodedLiveStateDocument
  history : DecodedCertifiedHistory
    (rProduction live.global.global.rsucc)
    live.ordinaryArena live.rootArena live.insertionHistory

def WireLiveInsertionDerivationDocument.decode
    (wire : WireLiveInsertionDerivationDocument) :
    Except String DecodedLiveInsertionDerivationDocument := do
  if wire.version != 2 then
    throw s!"unsupported CB live insertion-derivation version {wire.version}"
  let live ← wire.production_bound.decode
  let history ← decodeHistoryEvidence
    (rProduction live.global.global.rsucc)
    live.ordinaryArena live.rootArena live.insertionHistory
    wire.insertion_evidence
  return { live, history }

def WireLiveInsertionDerivationDocument.check
    (wire : WireLiveInsertionDerivationDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireLiveInsertionDerivationDocument.check_sound
    (wire : WireLiveInsertionDerivationDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedLiveInsertionDerivationDocument,
      wire.decode = .ok decoded ∧
      ∀ event ∈ decoded.live.insertionHistory, EventSound event := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireLiveInsertionDerivationDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.history.sound⟩

#print axioms EventEvidence.sound
#print axioms CertifiedHistory.sound
#print axioms DecodedCertifiedHistory.sound
#print axioms WireLiveInsertionDerivationDocument.check_sound

end ContextCalculus.CBLiveInsertionDerivation
