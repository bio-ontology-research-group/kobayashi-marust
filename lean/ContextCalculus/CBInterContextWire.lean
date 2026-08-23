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

structure WireInterContextRun where
  version : Nat
  production : WireProductionRun
  transfers : List WirePredTransfer
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

def WireInterContextRun.decode (wire : WireInterContextRun) :
    Except String DecodedInterContextRun := do
  if wire.version != 1 then
    throw s!"unsupported CB inter-context version {wire.version}"
  if wire.transfers.isEmpty then
    throw "CB inter-context evidence must contain at least one transfer"
  let production ← wire.production.decode
  let transfers ← wire.transfers.mapM (WirePredTransfer.decode production)
  return { production, transfers }

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

theorem WireInterContextRun.check_sound (wire : WireInterContextRun)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedInterContextRun,
      wire.decode = .ok decoded ∧
      ∀ transfer ∈ decoded.transfers,
        ∀ (D : Type) (model : TModel D),
          (∀ source ∈ decoded.production.source.ontology, valid model source) →
          valid model transfer.payload := by
  cases hdecode : wire.decode with
  | error message => simp [WireInterContextRun.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_⟩
      intro transfer _ D model hontology
      exact transfer.payload_valid model hontology

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
  retained := [⟨[literal 0], [literal 1]⟩]
  discarded := []
  trace := [⟨⟨[literal 0], [literal 1]⟩, .premise 0 []⟩]

private def productionExample : WireProductionRun where
  version := 1
  source := sourceExample
  contexts := [contextExample]

private def acceptedExample : WireInterContextRun where
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

#print axioms DecodedPredTransfer.payload_valid
#print axioms WireInterContextRun.check_sound

end ContextCalculus.CBInterContextWire
