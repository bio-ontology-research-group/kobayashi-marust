import ContextCalculus.CBInterContext
import ContextCalculus.CBProductionTraceWire

/-!
# Executable production CB inter-context payload evidence

This wire binds each ordinary Pred or nominal r-Pred sender payload to one
retained clause and the exact core of one context in a checked production run.
It checks the edge substitution and requires the serialized payload to be
clause-equivalent to `CBInterContext.predTransfer`.
-/

namespace ContextCalculus.CBInterContextWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire ContextCalculus.CBInterContext
open ContextCalculus.CBSourceWire

structure WirePredTransfer where
  sender_context_index : Nat
  sender_context_id : Nat
  retained_clause_index : Nat
  substitution : List WireSubstitutionEntry
  payload : WireClause
deriving FromJson, ToJson

structure WirePredProvider where
  retained_clause_index : Nat
  literal : WireLiteral
deriving FromJson, ToJson

structure WirePredArrival where
  transfer_index : Nat
  receiver_context_index : Nat
  receiver_context_id : Nat
  providers : List WirePredProvider
  result : WireClause
deriving FromJson, ToJson

structure WireInterContextRun where
  version : Nat
  production : WireProductionRun
  transfers : List WirePredTransfer
  arrivals : List WirePredArrival
deriving FromJson, ToJson

structure DecodedPredTransfer (production : DecodedProductionRun) where
  senderIndex : Fin production.contexts.length
  senderId : Nat
  sender_id_eq : (production.contexts.get senderIndex).contextId = senderId
  retainedIndex : Fin (production.contexts.get senderIndex).retained.length
  substitution : List (Int × FTerm)
  payload : FCL
  payload_equiv : clEquivT payload
    (predTransfer substitution
      (production.contexts.get senderIndex).core
      ((production.contexts.get senderIndex).retained.get retainedIndex))

def WirePredTransfer.decode (production : DecodedProductionRun)
    (wire : WirePredTransfer) : Except String (DecodedPredTransfer production) := do
  if hsender : wire.sender_context_index < production.contexts.length then
    let senderIndex : Fin production.contexts.length :=
      ⟨wire.sender_context_index, hsender⟩
    let sender := production.contexts.get senderIndex
    if hid : sender.contextId = wire.sender_context_id then
      if hretained : wire.retained_clause_index < sender.retained.length then
        let retainedIndex : Fin sender.retained.length :=
          ⟨wire.retained_clause_index, hretained⟩
        let variableIds := wire.substitution.map WireSubstitutionEntry.variableId
        if variableIds.Nodup then
          let substitution ← wire.substitution.mapM
            (WireSubstitutionEntry.decode production.source.bounds)
          let payload ← wire.payload.decode production.source.bounds
          let expected := predTransfer substitution sender.core
            (sender.retained.get retainedIndex)
          if hequivalent : clEquivT payload expected then
            return {
              senderIndex
              senderId := wire.sender_context_id
              sender_id_eq := hid
              retainedIndex
              substitution
              payload
              payload_equiv := hequivalent
            }
          else throw "Pred payload differs from the substituted sender clause and core"
        else throw "Pred transfer substitution contains a duplicate variable"
      else throw "Pred transfer retained-clause index is outside the sender context"
    else throw "Pred transfer sender id differs from its indexed context"
  else throw "Pred transfer sender-context index is outside the production run"

structure DecodedInterContextRun where
  production : DecodedProductionRun
  transfers : List (DecodedPredTransfer production)

structure DecodedPredProvider
    (receiver : DecodedProductionContext bounds ontology) where
  retainedIndex : Fin receiver.retained.length
  literal : FLit

def arrivalConclusion
    (receiver : DecodedProductionContext bounds ontology) :
    FCL → List (DecodedPredProvider receiver) → FCL
  | current, [] => current
  | current, provider :: rest =>
      arrivalConclusion receiver
        (resolvent (receiver.retained.get provider.retainedIndex)
          current provider.literal) rest

def arrivalStepsOk
    (receiver : DecodedProductionContext bounds ontology) :
    FCL → List (DecodedPredProvider receiver) → Bool
  | _, [] => true
  | current, provider :: rest =>
      decide (provider.literal ∈
        (receiver.retained.get provider.retainedIndex).head) &&
      decide (provider.literal ∈ current.body) &&
      arrivalStepsOk receiver
        (resolvent (receiver.retained.get provider.retainedIndex)
          current provider.literal) rest

structure DecodedPredArrival (decoded : DecodedInterContextRun) where
  transferIndex : Fin decoded.transfers.length
  receiverIndex : Fin decoded.production.contexts.length
  receiverId : Nat
  receiver_id_eq :
    (decoded.production.contexts.get receiverIndex).contextId = receiverId
  providers : List
    (DecodedPredProvider (decoded.production.contexts.get receiverIndex))
  steps_ok : arrivalStepsOk
    (decoded.production.contexts.get receiverIndex)
    (decoded.transfers.get transferIndex).payload providers = true
  result : FCL
  result_equiv : clEquivT result
    (arrivalConclusion (decoded.production.contexts.get receiverIndex)
      (decoded.transfers.get transferIndex).payload providers)

structure DecodedCompleteInterContextRun where
  base : DecodedInterContextRun
  arrivals : List (DecodedPredArrival base)

def WirePredProvider.decode
    (receiver : DecodedProductionContext bounds ontology)
    (wire : WirePredProvider) : Except String (DecodedPredProvider receiver) := do
  if hindex : wire.retained_clause_index < receiver.retained.length then
    let retainedIndex : Fin receiver.retained.length :=
      ⟨wire.retained_clause_index, hindex⟩
    let literal ← wire.literal.decode bounds
    return { retainedIndex, literal }
  else throw "Pred arrival provider index is outside the receiver retained clauses"

def WirePredArrival.decode (decoded : DecodedInterContextRun)
    (wire : WirePredArrival) : Except String (DecodedPredArrival decoded) := do
  if htransfer : wire.transfer_index < decoded.transfers.length then
    let transferIndex : Fin decoded.transfers.length :=
      ⟨wire.transfer_index, htransfer⟩
    if hreceiver : wire.receiver_context_index < decoded.production.contexts.length then
      let receiverIndex : Fin decoded.production.contexts.length :=
        ⟨wire.receiver_context_index, hreceiver⟩
      let receiver := decoded.production.contexts.get receiverIndex
      if hid : receiver.contextId = wire.receiver_context_id then
        let providers ← wire.providers.mapM (WirePredProvider.decode receiver)
        let payload := (decoded.transfers.get transferIndex).payload
        if hsteps : arrivalStepsOk receiver payload providers = true then
          let result ← wire.result.decode decoded.production.source.bounds
          let expected := arrivalConclusion receiver payload providers
          if hequivalent : clEquivT result expected then
            return {
              transferIndex
              receiverIndex
              receiverId := wire.receiver_context_id
              receiver_id_eq := hid
              providers
              steps_ok := hsteps
              result
              result_equiv := hequivalent
            }
          else throw "Pred arrival result differs from its checked resolution fold"
        else throw "Pred arrival provider does not discharge the current body literal"
      else throw "Pred arrival receiver id differs from its indexed context"
    else throw "Pred arrival receiver-context index is outside the production run"
  else throw "Pred arrival transfer index is outside the transfer list"

def WireInterContextRun.decode (wire : WireInterContextRun) :
    Except String DecodedCompleteInterContextRun := do
  if wire.version != 1 then
    throw s!"unsupported CB inter-context version {wire.version}"
  if wire.transfers.isEmpty then
    throw "CB inter-context evidence must contain at least one transfer"
  let production ← wire.production.decode
  let transfers ← wire.transfers.mapM (WirePredTransfer.decode production)
  let base : DecodedInterContextRun := { production, transfers }
  let arrivals ← wire.arrivals.mapM (WirePredArrival.decode base)
  return { base, arrivals }

def WireInterContextRun.check (wire : WireInterContextRun) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedPredTransfer.payload_valid
    (transfer : DecodedPredTransfer production)
    {D : Type} (model : TModel D)
    (hontology : ∀ source ∈ production.source.ontology, valid model source) :
    valid model transfer.payload := by
  let sender := production.contexts.get transfer.senderIndex
  let sourceClause := sender.retained.get transfer.retainedIndex
  have hcontextual : ContextValid model sender.core sourceClause := by
    intro assignment hcore
    exact sender.retained_sound model assignment hontology hcore sourceClause
      (List.get_mem sender.retained transfer.retainedIndex)
  have hexpected := predTransfer_sound model sender.core sourceClause
    transfer.substitution hcontextual
  intro assignment
  exact sat_of_clEquivT transfer.payload_equiv (hexpected assignment)

theorem arrivalConclusion_contextValid
    (receiver : DecodedProductionContext bounds ontology)
    (providers : List (DecodedPredProvider receiver))
    {D : Type} (model : TModel D) (current : FCL)
    (hcurrent : ContextValid model receiver.core current)
    (hontology : ∀ source ∈ ontology, valid model source)
    (hsteps : arrivalStepsOk receiver current providers = true) :
    ContextValid model receiver.core
      (arrivalConclusion receiver current providers) := by
  induction providers generalizing current with
  | nil => exact hcurrent
  | cons provider rest ih =>
      simp only [arrivalStepsOk, Bool.and_eq_true] at hsteps
      have hprovider : ContextValid model receiver.core
          (receiver.retained.get provider.retainedIndex) := by
        intro assignment hcore
        exact receiver.retained_sound model assignment hontology hcore _
          (List.get_mem receiver.retained provider.retainedIndex)
      have hresolved := resolveContextual_sound model receiver.core
        (receiver.retained.get provider.retainedIndex) current provider.literal
        hprovider hcurrent (of_decide_eq_true hsteps.1.1)
        (of_decide_eq_true hsteps.1.2)
      exact ih _ hresolved hsteps.2

theorem DecodedPredArrival.result_contextValid
    (arrival : DecodedPredArrival decoded)
    {D : Type} (model : TModel D)
    (hontology : ∀ source ∈ decoded.production.source.ontology,
      valid model source) :
    ContextValid model
      (decoded.production.contexts.get arrival.receiverIndex).core
      arrival.result := by
  let receiver := decoded.production.contexts.get arrival.receiverIndex
  let transfer := decoded.transfers.get arrival.transferIndex
  have hpayloadValid : valid model transfer.payload :=
    transfer.payload_valid model hontology
  have hpayloadContext : ContextValid model receiver.core transfer.payload := by
    intro assignment _
    exact hpayloadValid assignment
  have hfold := arrivalConclusion_contextValid receiver arrival.providers model
    transfer.payload hpayloadContext hontology arrival.steps_ok
  intro assignment hcore
  exact sat_of_clEquivT arrival.result_equiv (hfold assignment hcore)

theorem WireInterContextRun.check_sound (wire : WireInterContextRun)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCompleteInterContextRun,
      wire.decode = .ok decoded ∧
      (∀ transfer ∈ decoded.base.transfers,
        ∀ (D : Type) (model : TModel D),
          (∀ source ∈ decoded.base.production.source.ontology,
            valid model source) →
          valid model transfer.payload) ∧
      (∀ arrival ∈ decoded.arrivals,
        ∀ (D : Type) (model : TModel D),
          (∀ source ∈ decoded.base.production.source.ontology,
            valid model source) →
          ContextValid model
            (decoded.base.production.contexts.get arrival.receiverIndex).core
            arrival.result) := by
  cases hdecode : wire.decode with
  | error message => simp [WireInterContextRun.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_, ?_⟩
      · intro transfer _ D model hontology
        exact transfer.payload_valid model hontology
      · intro arrival _ D model hontology
        exact arrival.result_contextValid model hontology

private def x : WireTerm := .var 0
private def concept (id : Nat) : WirePredicate := .concept id x
private def literal (id : Nat) : WireLiteral := .predicate (concept id)

private def sourceExample : WireSourceBinding where
  version := 1
  concept_count := 2
  role_count := 0
  function_count := 0
  individual_count := 0
  source_clauses := [.gci [0] [1]]
  role_chains := []
  ontology := [⟨[literal 0], [literal 1]⟩]

private def contextExample : WireProductionContext where
  context_id := 7
  root := false
  query_concept := none
  core := [concept 0]
  retained := [⟨[literal 0], [literal 1]⟩, ⟨[], [literal 0]⟩]
  discarded := []
  trace := [
    ⟨⟨[literal 0], [literal 1]⟩, .premise 0 []⟩,
    ⟨⟨[], [literal 0]⟩, .assumption 0⟩]

private def productionExample : WireProductionRun where
  version := 1
  source := sourceExample
  contexts := [contextExample]

def acceptedExample : WireInterContextRun where
  version := 1
  production := productionExample
  transfers := [{
    sender_context_index := 0
    sender_context_id := 7
    retained_clause_index := 0
    substitution := []
    -- Production sort/dedup removes the duplicate core/body C0 literal.
    payload := ⟨[literal 0], [literal 1]⟩
  }]
  arrivals := [{
    transfer_index := 0
    receiver_context_index := 0
    receiver_context_id := 7
    providers := [{ retained_clause_index := 1, literal := literal 0 }]
    result := ⟨[], [literal 1]⟩
  }]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedExample.check = .ok true := by native_decide

private def forgedSenderExample : WireInterContextRun :=
  { acceptedExample with transfers :=
      acceptedExample.transfers.map (fun transfer =>
        { transfer with sender_context_id := 8 }) }

example : rejected forgedSenderExample.check = true := by native_decide

private def forgedPayloadExample : WireInterContextRun :=
  { acceptedExample with transfers :=
      acceptedExample.transfers.map (fun transfer =>
        { transfer with payload := ⟨[], [literal 1]⟩ }) }

example : rejected forgedPayloadExample.check = true := by native_decide

private def forgedProviderExample : WireInterContextRun :=
  { acceptedExample with arrivals :=
      acceptedExample.arrivals.map (fun arrival =>
        { arrival with providers :=
          [{ retained_clause_index := 0, literal := literal 0 }] }) }

example : rejected forgedProviderExample.check = true := by native_decide

private def forgedArrivalResultExample : WireInterContextRun :=
  { acceptedExample with arrivals :=
      acceptedExample.arrivals.map (fun arrival =>
        { arrival with result := ⟨[], [literal 0]⟩ }) }

example : rejected forgedArrivalResultExample.check = true := by native_decide

#print axioms DecodedPredTransfer.payload_valid
#print axioms arrivalConclusion_contextValid
#print axioms DecodedPredArrival.result_contextValid
#print axioms WireInterContextRun.check_sound

end ContextCalculus.CBInterContextWire
