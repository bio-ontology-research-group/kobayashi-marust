import ContextCalculus.CBLiveStateWire

/-!
# Source-bound chronological CB context proofs

This wire checks the semantic proof DAG needed by the source-exact taxonomy
boundary without importing an abstract global-closure certificate. Local nodes
reuse `CBProductionTrace`; Pred nodes connect a sender proof to receiver
provider proofs through the exact production transfer and resolution fold.
-/

namespace ContextCalculus.CBStandaloneContextProofWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire ContextCalculus.CBInterContext
open ContextCalculus.CBLiveStateWire

inductive WireStandaloneEvidence where
  | local (prior_nodes : List Nat) (trace : List WireProductionEntry)
  | pred (sender_node : Nat) (provider_nodes : List Nat)
      (edge_label : WireTerm) (payload : WireClause)
      (matched : List WirePredicate)
deriving FromJson, ToJson

structure WireStandaloneNode where
  core : List WirePredicate
  clause : WireClause
  evidence : WireStandaloneEvidence
deriving FromJson, ToJson

structure DecodedStandaloneNode (ontology : List FCL) where
  core : List FPred
  clause : FCL
  contextValid : ∀ {D : Type} (model : TModel D),
    (∀ source ∈ ontology, valid model source) →
    ContextValid model core clause

private def assumptionClause (predicate : FPred) : FCL :=
  ⟨[], [.P predicate]⟩

private def priorEntriesFrom : Nat → List FCL → List Entry
  | _, [] => []
  | index, clause :: rest =>
      (clause, .assumption index) :: priorEntriesFrom (index + 1) rest

private def priorEntries (clauses : List FCL) : List Entry :=
  priorEntriesFrom 0 clauses

private def decodePrior (nodes : List (DecodedStandaloneNode ontology))
    (indices : List Nat) : Except String (List (DecodedStandaloneNode ontology)) :=
  indices.mapM fun index =>
    match nodes[index]? with
    | some node => pure node
    | none => throw "standalone CB proof references a non-earlier node"

private theorem assumptions_contextValid
    (nodes : List (DecodedStandaloneNode ontology))
    (core : List FPred)
    (hcores : ∀ node ∈ nodes, node.core = core)
    {D : Type} (model : TModel D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (assignment : Int → D)
    (hcore : ∀ predicate ∈ core, model.evalL assignment (.P predicate)) :
    ∀ assumption ∈ nodes.map (·.clause) ++ core.map assumptionClause,
      HoldsAt model assignment assumption := by
  intro assumption hassumption
  rcases List.mem_append.mp hassumption with hnode | hcoreAssumption
  · rcases List.mem_map.mp hnode with ⟨node, hnodeNodes, hclause⟩
    subst assumption
    exact node.contextValid model hontology assignment
      (by
        intro predicate hpredicate
        exact hcore predicate (by
          rw [← hcores node hnodeNodes]
          exact hpredicate))
  · rcases List.mem_map.mp hcoreAssumption with ⟨predicate, hpredicate, rfl⟩
    intro _
    exact ⟨.P predicate, by simp [assumptionClause], hcore predicate hpredicate⟩

def WireStandaloneNode.decodeLocal
    (bounds : Bounds) (ontology : List FCL)
    (nodes : List (DecodedStandaloneNode ontology))
    (wire : WireStandaloneNode) (indices : List Nat)
    (wireTrace : List WireProductionEntry) :
    Except String (DecodedStandaloneNode ontology) := do
  if wire.core.Nodup then pure () else
    throw "standalone CB node core contains duplicates"
  let core ← wire.core.mapM (WirePredicate.decode bounds)
  if hcoreNodup : core.Nodup then pure () else
    throw "decoded standalone CB node core contains duplicates"
  let prior ← decodePrior nodes indices
  if hpriorCores : ∀ node ∈ prior, node.core = core then
    let trace ← wireTrace.mapM (WireProductionEntry.decode bounds)
    let initialEntries := priorEntries (prior.map (·.clause))
    let combined := initialEntries ++ trace
    let assumptions := prior.map (·.clause) ++ core.map assumptionClause
    if hcheck : check ontology assumptions combined = true then
      let clause ← wire.clause.decode bounds
      if hresult : clause ∈ terminal combined then
        return {
          core
          clause
          contextValid := by
            intro D model hontology assignment hcore
            exact check_sound model assignment hontology
              (assumptions_contextValid prior core hpriorCores model hontology
                assignment hcore)
              hcheck clause hresult
        }
      else throw "standalone CB local trace omits its claimed result"
    else throw "standalone CB local production trace was rejected"
  else throw "local standalone CB premise uses a different context core"

private structure DecodedPredProvider (ontology : List FCL)
    (core : List FPred) where
  node : DecodedStandaloneNode ontology
  core_eq : node.core = core
  matched : FPred
  matched_in_head : FLit.P matched ∈ node.clause.head

private def decodePredProviders (bounds : Bounds)
    (nodes : List (DecodedStandaloneNode ontology)) (core : List FPred) :
    List Nat → List WirePredicate →
      Except String (List (DecodedPredProvider ontology core))
  | [], [] => pure []
  | index :: indices, wireMatched :: rest => do
      let node ← match nodes[index]? with
        | some node => pure node
        | none => throw "standalone CB Pred provider is not earlier"
      if hcore : node.core = core then
        let matched ← wireMatched.decode bounds
        if hmatched : FLit.P matched ∈ node.clause.head then
          let tail ← decodePredProviders bounds nodes core indices rest
          let provider : DecodedPredProvider ontology core := {
            node := node
            core_eq := hcore
            matched := matched
            matched_in_head := hmatched
          }
          return provider :: tail
        else throw "standalone CB Pred matched literal is absent from provider head"
      else throw "standalone CB Pred provider uses the wrong receiver core"
  | _, _ => throw "standalone CB Pred provider and matched lengths differ"

private def predConclusion : FCL → List (DecodedPredProvider ontology core) → FCL
  | current, [] => current
  | current, provider :: rest =>
      predConclusion (resolvent provider.node.clause current (.P provider.matched)) rest

private def predStepsOk : FCL → List (DecodedPredProvider ontology core) → Bool
  | _, [] => true
  | current, provider :: rest =>
      decide (FLit.P provider.matched ∈ current.body) &&
      predStepsOk
        (resolvent provider.node.clause current (.P provider.matched)) rest

private theorem predConclusion_contextValid
    (providers : List (DecodedPredProvider ontology core))
    {D : Type} (model : TModel D)
    (hontology : ∀ source ∈ ontology, valid model source)
    (current : FCL) (hcurrent : ContextValid model core current)
    (hsteps : predStepsOk current providers = true) :
    ContextValid model core (predConclusion current providers) := by
  induction providers generalizing current with
  | nil => exact hcurrent
  | cons provider rest ih =>
      simp only [predStepsOk, Bool.and_eq_true] at hsteps
      have hprovider : ContextValid model core provider.node.clause := by
        intro assignment hcore
        exact provider.node.contextValid model hontology assignment (by
          intro predicate hpredicate
          exact hcore predicate (by
            rw [provider.core_eq] at hpredicate
            exact hpredicate))
      have hresolved := resolveContextual_sound model core
        provider.node.clause current (.P provider.matched)
        hprovider hcurrent provider.matched_in_head
        (of_decide_eq_true hsteps.1)
      exact ih _ hresolved hsteps.2

def WireStandaloneNode.decodePred
    (bounds : Bounds) (ontology : List FCL)
    (nodes : List (DecodedStandaloneNode ontology))
    (wire : WireStandaloneNode) (senderIndex : Nat)
    (providerIndices : List Nat) (edgeWire : WireTerm)
    (payloadWire : WireClause) (matchedWire : List WirePredicate) :
    Except String (DecodedStandaloneNode ontology) := do
  if wire.core.Nodup then pure () else
    throw "standalone CB node core contains duplicates"
  let core ← wire.core.mapM (WirePredicate.decode bounds)
  if hcoreNodup : core.Nodup then pure () else
    throw "decoded standalone CB node core contains duplicates"
  let sender ← match nodes[senderIndex]? with
    | some node => pure node
    | none => throw "standalone CB Pred sender is not earlier"
  let providers ← decodePredProviders bounds nodes core providerIndices matchedWire
  let edge ← edgeWire.decode bounds
  let payload ← payloadWire.decode bounds
  let expectedPayload := predTransfer (predBackwardSubstitution edge)
    sender.core sender.clause
  if hpayload : clEquivT payload expectedPayload then
    if hsteps : predStepsOk payload providers = true then
      let clause ← wire.clause.decode bounds
      if hresult : clEquivT clause (predConclusion payload providers) then
        return {
          core
          clause
          contextValid := by
            intro D model hontology
            have hsender := sender.contextValid model hontology
            have hpayloadExpected := predTransfer_sound model sender.core sender.clause
              (predBackwardSubstitution edge) hsender
            have hpayloadValid : valid model payload := by
              intro assignment
              exact sat_of_clEquivT hpayload (hpayloadExpected assignment)
            have hfold := predConclusion_contextValid providers model hontology payload
              (by intro assignment _; exact hpayloadValid assignment) hsteps
            intro assignment hcore
            exact sat_of_clEquivT hresult (hfold assignment hcore)
        }
      else throw "standalone CB Pred result differs from its resolution fold"
    else throw "standalone CB Pred provider does not discharge the payload body"
  else throw "standalone CB Pred payload differs from the exact sender transfer"

def WireStandaloneNode.decode
    (bounds : Bounds) (ontology : List FCL)
    (nodes : List (DecodedStandaloneNode ontology))
    (wire : WireStandaloneNode) :
    Except String (DecodedStandaloneNode ontology) :=
  match wire.evidence with
  | .local prior trace => wire.decodeLocal bounds ontology nodes prior trace
  | .pred sender providers edge payload matched =>
      wire.decodePred bounds ontology nodes sender providers edge payload matched

private def decodeNodesChronological (bounds : Bounds) (ontology : List FCL) :
    List (DecodedStandaloneNode ontology) → List WireStandaloneNode →
      Except String (List (DecodedStandaloneNode ontology))
  | done, [] => pure done
  | done, wire :: rest => do
      let node ← wire.decode bounds ontology done
      decodeNodesChronological bounds ontology (done ++ [node]) rest

structure WireStandaloneProof where
  version : Nat
  nodes : List WireStandaloneNode
deriving FromJson, ToJson

structure DecodedStandaloneProof (ontology : List FCL) where
  nodes : List (DecodedStandaloneNode ontology)

def WireStandaloneProof.decode (bounds : Bounds) (ontology : List FCL)
    (wire : WireStandaloneProof) : Except String (DecodedStandaloneProof ontology) := do
  if wire.version != 1 then
    throw s!"unsupported standalone CB context-proof version {wire.version}"
  return { nodes := ← decodeNodesChronological bounds ontology [] wire.nodes }

def WireStandaloneProof.check (bounds : Bounds) (ontology : List FCL)
    (wire : WireStandaloneProof) : Except String Bool := do
  let _ ← wire.decode bounds ontology
  return true

structure WireStandaloneDocument where
  version : Nat
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  individual_count : Nat
  ontology : List WireClause
  proof : WireStandaloneProof
deriving FromJson, ToJson

def WireStandaloneDocument.check (wire : WireStandaloneDocument) :
    Except String Bool := do
  if wire.version != 1 then
    throw s!"unsupported standalone CB context-proof document version {wire.version}"
  let bounds : Bounds :=
    { concepts := wire.concept_count
      roles := wire.role_count
      functions := wire.function_count
      individuals := wire.individual_count }
  let ontology ← wire.ontology.mapM (WireClause.decode bounds)
  wire.proof.check bounds ontology

end ContextCalculus.CBStandaloneContextProofWire
