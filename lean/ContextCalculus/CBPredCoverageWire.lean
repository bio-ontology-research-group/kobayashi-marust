import ContextCalculus.CBPredEnumeration

/-!
# Executable exhaustive Pred Cartesian coverage

For one accepted transfer/receiver pair, this checker recomputes the complete
provider plan from the retained receiver snapshot, enumerates every Cartesian
selection, and requires a strengthening accepted arrival for each raw result.
The wire cannot omit, duplicate, or forge a generated selection because its
decoded signatures must equal the recomputed list exactly.
-/

namespace ContextCalculus.CBPredCoverageWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire ContextCalculus.CBInterContext
open ContextCalculus.CBInterContextWire ContextCalculus.CBPredEnumeration

structure WireGeneratedPredResult where
  providers : List WirePredProvider
  strengthening_arrival_index : Nat
deriving FromJson, ToJson

structure WirePredCoverage where
  transfer_index : Nat
  receiver_context_index : Nat
  receiver_context_id : Nat
  generated : List WireGeneratedPredResult
deriving FromJson, ToJson

structure WirePredCoverageDocument where
  version : Nat
  inter_context : WireInterContextRun
  coverages : List WirePredCoverage
deriving FromJson, ToJson

abbrev SelectionSignature := List (Nat × FLit)

def expectedSignatures
    (receiver : DecodedProductionContext bounds ontology) (payload : FCL) :
    List SelectionSignature :=
  match providerPlan receiver.retained payload.body with
  | none => []
  | some (dimensions, _) =>
      (cartesianSelections (dimensions.map Prod.snd)).map fun selection =>
        (dimensions.zip selection).map fun entry =>
          (entry.2.val, entry.1.1)

structure DecodedGeneratedPredResult
    (decoded : DecodedCompleteInterContextRun)
    (transferIndex : Fin decoded.base.transfers.length)
    (receiverIndex : Fin decoded.base.production.contexts.length) where
  providers : List (DecodedPredProvider
    (decoded.base.production.contexts.get receiverIndex))
  steps_ok : arrivalStepsOk
    (decoded.base.production.contexts.get receiverIndex)
    (decoded.base.transfers.get transferIndex).payload providers = true
  strengtheningArrivalIndex : Fin decoded.arrivals.length
  same_transfer :
    (decoded.arrivals.get strengtheningArrivalIndex).transferIndex.val =
      transferIndex.val
  same_receiver :
    (decoded.arrivals.get strengtheningArrivalIndex).receiverIndex.val =
      receiverIndex.val
  strengthens : Strengthens
    (decoded.arrivals.get strengtheningArrivalIndex).result
    (arrivalConclusion
      (decoded.base.production.contexts.get receiverIndex)
      (decoded.base.transfers.get transferIndex).payload providers)

def DecodedGeneratedPredResult.signature
    (generated : DecodedGeneratedPredResult decoded transfer receiver) :
    SelectionSignature :=
  generated.providers.map fun provider =>
    (provider.retainedIndex.val, provider.literal)

def WireGeneratedPredResult.decode
    (decoded : DecodedCompleteInterContextRun)
    (transferIndex : Fin decoded.base.transfers.length)
    (receiverIndex : Fin decoded.base.production.contexts.length)
    (wire : WireGeneratedPredResult) :
    Except String (DecodedGeneratedPredResult decoded transferIndex receiverIndex) := do
  let receiver := decoded.base.production.contexts.get receiverIndex
  let providers ← wire.providers.mapM (WirePredProvider.decode receiver)
  let payload := (decoded.base.transfers.get transferIndex).payload
  if hsteps : arrivalStepsOk receiver payload providers = true then
    if harrival : wire.strengthening_arrival_index < decoded.arrivals.length then
      let arrivalIndex : Fin decoded.arrivals.length :=
        ⟨wire.strengthening_arrival_index, harrival⟩
      let arrival := decoded.arrivals.get arrivalIndex
      if htransfer : arrival.transferIndex.val = transferIndex.val then
        if hreceiver : arrival.receiverIndex.val = receiverIndex.val then
          let raw := arrivalConclusion receiver payload providers
          if hstrengthens : Strengthens arrival.result raw then
            return {
              providers
              steps_ok := hsteps
              strengtheningArrivalIndex := arrivalIndex
              same_transfer := htransfer
              same_receiver := hreceiver
              strengthens := hstrengthens
            }
          else throw "retained Pred arrival does not strengthen its raw Cartesian result"
        else throw "Pred coverage arrival belongs to a different receiver"
      else throw "Pred coverage arrival belongs to a different transfer"
    else throw "Pred coverage strengthening-arrival index is outside the arrival list"
  else throw "Pred coverage selection is not a valid receiver resolution fold"

structure DecodedPredCoverage (decoded : DecodedCompleteInterContextRun) where
  transferIndex : Fin decoded.base.transfers.length
  receiverIndex : Fin decoded.base.production.contexts.length
  receiverId : Nat
  receiver_id_eq :
    (decoded.base.production.contexts.get receiverIndex).contextId = receiverId
  receiver_is_target :
    (decoded.base.transfers.get transferIndex).receiverIndex.val =
      receiverIndex.val
  generated : List
    (DecodedGeneratedPredResult decoded transferIndex receiverIndex)
  signatures_exact : generated.map (·.signature) =
    expectedSignatures
      (decoded.base.production.contexts.get receiverIndex)
      (decoded.base.transfers.get transferIndex).payload

def WirePredCoverage.decode (decoded : DecodedCompleteInterContextRun)
    (wire : WirePredCoverage) : Except String (DecodedPredCoverage decoded) := do
  if htransfer : wire.transfer_index < decoded.base.transfers.length then
    let transferIndex : Fin decoded.base.transfers.length :=
      ⟨wire.transfer_index, htransfer⟩
    if hreceiver : wire.receiver_context_index <
        decoded.base.production.contexts.length then
      let receiverIndex : Fin decoded.base.production.contexts.length :=
        ⟨wire.receiver_context_index, hreceiver⟩
      let receiver := decoded.base.production.contexts.get receiverIndex
      if hid : receiver.contextId = wire.receiver_context_id then
        let transfer := decoded.base.transfers.get transferIndex
        if htarget : transfer.receiverIndex.val = receiverIndex.val then
          let generated ← wire.generated.mapM
            (WireGeneratedPredResult.decode decoded transferIndex receiverIndex)
          let expected := expectedSignatures receiver transfer.payload
          if hexact : generated.map (·.signature) = expected then
            return {
              transferIndex
              receiverIndex
              receiverId := wire.receiver_context_id
              receiver_id_eq := hid
              receiver_is_target := htarget
              generated
              signatures_exact := hexact
            }
          else throw "Pred coverage omits, duplicates, or reorders a Cartesian selection"
        else throw "Pred coverage receiver differs from the transfer target"
      else throw "Pred coverage receiver id differs from its indexed context"
    else throw "Pred coverage receiver-context index is outside the production run"
  else throw "Pred coverage transfer index is outside the transfer list"

structure DecodedPredCoverageDocument where
  interContext : DecodedCompleteInterContextRun
  coverages : List (DecodedPredCoverage interContext)
  transfer_coverage_exact : coverages.map (fun coverage =>
      coverage.transferIndex.val) =
    List.range interContext.base.transfers.length

def WirePredCoverageDocument.decode (wire : WirePredCoverageDocument) :
    Except String DecodedPredCoverageDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB Pred-coverage version {wire.version}"
  if wire.coverages.isEmpty then
    throw "CB Pred coverage must contain at least one transfer/receiver pair"
  let interContext ← wire.inter_context.decode
  let coverages ← wire.coverages.mapM (WirePredCoverage.decode interContext)
  let coveredTransfers := coverages.map (fun coverage =>
    coverage.transferIndex.val)
  let expectedTransfers := List.range interContext.base.transfers.length
  if hexact : coveredTransfers = expectedTransfers then
    return { interContext, coverages, transfer_coverage_exact := hexact }
  else throw "Pred coverage must cover every transfer exactly once and in order"

def WirePredCoverageDocument.check (wire : WirePredCoverageDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem DecodedGeneratedPredResult.raw_contextValid
    (generated : DecodedGeneratedPredResult decoded transfer receiver)
    {D : Type} (model : TModel D)
    (hretained : ProductionRetainedValid decoded.base.production model) :
    ContextValid model
      (decoded.base.production.contexts.get receiver).core
      (arrivalConclusion
        (decoded.base.production.contexts.get receiver)
        (decoded.base.transfers.get transfer).payload generated.providers) := by
  let arrival := decoded.arrivals.get generated.strengtheningArrivalIndex
  have harrival := arrival.result_contextValid model hretained
  have hsameReceiver : arrival.receiverIndex = receiver := by
    apply Fin.ext
    exact generated.same_receiver
  rw [hsameReceiver] at harrival
  exact ContextValid.of_strengthens model _ generated.strengthens harrival

theorem WirePredCoverageDocument.check_sound
    (wire : WirePredCoverageDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedPredCoverageDocument,
      wire.decode = .ok decoded ∧
      decoded.coverages.map (fun coverage => coverage.transferIndex.val) =
        List.range decoded.interContext.base.transfers.length ∧
      (∀ coverage ∈ decoded.coverages,
          (decoded.interContext.base.transfers.get
            coverage.transferIndex).receiverIndex.val =
              coverage.receiverIndex.val ∧
          coverage.generated.map (·.signature) =
            expectedSignatures
              (decoded.interContext.base.production.contexts.get
                coverage.receiverIndex)
              (decoded.interContext.base.transfers.get
                coverage.transferIndex).payload ∧
          ∀ generated ∈ coverage.generated,
            ∀ (D : Type) (model : TModel D),
              ProductionRetainedValid
                decoded.interContext.base.production model →
              ContextValid model
                (decoded.interContext.base.production.contexts.get
                  coverage.receiverIndex).core
                (arrivalConclusion
                  (decoded.interContext.base.production.contexts.get
                    coverage.receiverIndex)
                  (decoded.interContext.base.transfers.get
                    coverage.transferIndex).payload generated.providers)) := by
  cases hdecode : wire.decode with
  | error message => simp [WirePredCoverageDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.transfer_coverage_exact, ?_⟩
      intro coverage _
      refine ⟨coverage.receiver_is_target, coverage.signatures_exact, ?_⟩
      intro generated _ D model hretained
      exact generated.raw_contextValid model hretained

private def acceptedCoverageExample : WirePredCoverageDocument where
  version := 1
  inter_context := CBInterContextWire.acceptedExample
  coverages := [{
    transfer_index := 0
    receiver_context_index := 0
    receiver_context_id := 7
    generated := [{
      providers := [{
        retained_clause_index := 1
        literal := .predicate (.concept 0 (.var 0))
      }]
      strengthening_arrival_index := 0
    }]
  }]

private def rejected (result : Except String Bool) : Bool :=
  match result with | .error _ => true | .ok _ => false

example : acceptedCoverageExample.check = .ok true := by native_decide

private def omittedSelectionExample : WirePredCoverageDocument :=
  { acceptedCoverageExample with coverages :=
      acceptedCoverageExample.coverages.map (fun coverage =>
        { coverage with generated := [] }) }

example : rejected omittedSelectionExample.check = true := by native_decide

private def forgedProviderExample : WirePredCoverageDocument :=
  { acceptedCoverageExample with coverages :=
      acceptedCoverageExample.coverages.map (fun coverage =>
        { coverage with generated := coverage.generated.map (fun generated =>
          { generated with providers := [{
            retained_clause_index := 0
            literal := .predicate (.concept 0 (.var 0))
          }] }) }) }

example : rejected forgedProviderExample.check = true := by native_decide

private def forgedArrivalIndexExample : WirePredCoverageDocument :=
  { acceptedCoverageExample with coverages :=
      acceptedCoverageExample.coverages.map (fun coverage =>
        { coverage with generated := coverage.generated.map (fun generated =>
          { generated with strengthening_arrival_index := 1 }) }) }

example : rejected forgedArrivalIndexExample.check = true := by native_decide

private def duplicatedTransferCoverageExample : WirePredCoverageDocument :=
  { acceptedCoverageExample with coverages :=
      acceptedCoverageExample.coverages ++ acceptedCoverageExample.coverages }

example : rejected duplicatedTransferCoverageExample.check = true := by native_decide

#print axioms DecodedGeneratedPredResult.raw_contextValid
#print axioms WirePredCoverageDocument.check_sound

end ContextCalculus.CBPredCoverageWire
