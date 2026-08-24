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

private def requireSome (message : String) : Option α → Except String α
  | some value => pure value
  | none => throw message

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

structure WireLiveSubstitution where
  variable_id : Nat
  value : Nat
deriving FromJson, ToJson

structure WireLiveRuleEvidence where
  kind : String
  ontology_index : Option Nat
  instantiated_source : Option WireLiveClause
  context_clause_ids : Option (List Nat)
  matched_predicates : Option (List WireLivePredicate)
  substitution : Option (List WireLiveSubstitution)
  source_clause_id : Option Nat
  common : Option Nat
  first : Option Nat
  second : Option Nat
  equality_clause_id : Option Nat
  other_clause_id : Option Nat
  left : Option Nat
  right : Option Nat
  literal : Option WireLiveLiteral
  consumer_clause_id : Option Nat
  provider_clause_id : Option Nat
  bridge_clause_id : Option Nat
  ground : Option WireLivePredicate
  general : Option WireLivePredicate
  term : Option Nat
  sender_context_index : Option Nat
  sender_clause_id : Option Nat
  edge_label : Option Nat
  payload : Option WireLiveClause
  provider_clause_ids : Option (List Nat)
deriving FromJson, ToJson

private def WireLiveRuleEvidence.hasPredFields (wire : WireLiveRuleEvidence) : Bool :=
  wire.sender_context_index.isSome || wire.sender_clause_id.isSome ||
  wire.edge_label.isSome || wire.payload.isSome || wire.provider_clause_ids.isSome

structure WireLiveInsertionEvent where
  sequence : Nat
  context_index : Nat
  root : Bool
  clause_id : Nat
  origin_hint : String
  origin_index : Option Nat
  rule_hint : Option String
  rule_evidence : Option WireLiveRuleEvidence
deriving FromJson, ToJson

structure WireLiveContext where
  context_index : Nat
  context_id : Nat
  root : Bool
  nominal_ground : Bool
  query_concept : Option Nat
  core : List WireLivePredicate
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
  concept_count : Nat
  role_count : Nat
  function_count : Nat
  source_individual_count : Nat
  runtime_individual_count : Nat
  source_ontology : List WireLiveClause
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

def WireLiveSubstitution.decode (bounds : Bounds) (bits : Nat)
    (wire : WireLiveSubstitution) : Except String (Int × FTerm) := do
  let decodedVariable ← decodeRawTerm bounds bits wire.variable_id
  let value ← decodeRawTerm bounds bits wire.value
  match decodedVariable with
  | .var index => return (index, value)
  | _ => throw "CB live Hyper substitution key is not a variable"

structure DecodedLiveHyperPremise where
  clauseId : Nat
  clause : FCL
  matched : FPred
  matched_in_head : FLit.P matched ∈ clause.head

def decodeLiveHyperPremises (bounds : Bounds) (bits : Nat) (arena : List FCL) :
    List Nat → List WireLivePredicate → Except String (List DecodedLiveHyperPremise)
  | [], [] => pure []
  | clauseId :: clauseIds, wirePredicate :: wirePredicates => do
      let clause ← match arena[clauseId]? with
        | some clause => pure clause
        | none => throw "CB live Hyper premise id is outside its context arena"
      let matched ← wirePredicate.decode bounds bits
      if hmatched : FLit.P matched ∈ clause.head then
        return { clauseId, clause, matched, matched_in_head := hmatched } ::
          (← decodeLiveHyperPremises bounds bits arena clauseIds wirePredicates)
      else throw "CB live Hyper matched predicate is absent from its premise head"
  | _, _ => throw "CB live Hyper premise and matched-predicate lengths differ"

structure DecodedLiveHyperEvidence (production : DecodedProductionRun) where
  ontologyIndex : Nat
  instantiatedSource : FCL
  substitution : List (Int × FTerm)
  substitution_nodup : (substitution.map Prod.fst).Nodup
  source_step_valid : CBProductionTrace.stepOk production.source.ontology [] []
    instantiatedSource (.premise ontologyIndex substitution) = true
  premises : List DecodedLiveHyperPremise

def WireLiveRuleEvidence.decodeHyper (production : DecodedProductionRun)
    (bits : Nat) (arena : List FCL) (wire : WireLiveRuleEvidence) :
    Except String (DecodedLiveHyperEvidence production) := do
  if wire.kind != "hyper" then
    throw s!"unsupported CB live rule-evidence kind {wire.kind}"
  let ontologyIndex ← requireSome
    "CB live Hyper evidence omits its ontology index"
    wire.ontology_index
  let sourceWire ← requireSome
    "CB live Hyper evidence omits its instantiated source"
    wire.instantiated_source
  let clauseIds ← requireSome
    "CB live Hyper evidence omits its context premises"
    wire.context_clause_ids
  let matchedWires ← requireSome
    "CB live Hyper evidence omits its matched predicates"
    wire.matched_predicates
  let substitutionWire ← requireSome
    "CB live Hyper evidence omits its substitution"
    wire.substitution
  if wire.source_clause_id.isSome ∨ wire.common.isSome ∨ wire.first.isSome ∨
      wire.second.isSome ∨ wire.equality_clause_id.isSome ∨
      wire.other_clause_id.isSome ∨ wire.left.isSome ∨ wire.right.isSome ∨
      wire.literal.isSome ∨ wire.consumer_clause_id.isSome ∨
      wire.provider_clause_id.isSome ∨ wire.bridge_clause_id.isSome ∨
      wire.ground.isSome ∨ wire.general.isSome ∨ wire.term.isSome ∨
      wire.hasPredFields = true then
    throw "CB live Hyper evidence carries fields from another rule"
  let instantiatedSource ← sourceWire.decode production.bounds bits
  let substitution ← substitutionWire.mapM
    (WireLiveSubstitution.decode production.bounds bits)
  if hsubstitution : (substitution.map Prod.fst).Nodup then
  if hsource : CBProductionTrace.stepOk production.source.ontology [] []
      instantiatedSource (.premise ontologyIndex substitution) = true then
    let premises ← decodeLiveHyperPremises production.bounds bits arena
      clauseIds matchedWires
    return {
      ontologyIndex
      instantiatedSource
      substitution
      substitution_nodup := hsubstitution
      source_step_valid := hsource
      premises
    }
  else throw "CB live Hyper source instantiation was rejected"
  else throw "CB live Hyper substitution repeats a variable"

theorem DecodedLiveHyperEvidence.source_sound
    (evidence : DecodedLiveHyperEvidence production)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ production.source.ontology, valid model source) :
    CBProductionTrace.HoldsAt model assignment evidence.instantiatedSource := by
  exact CBProductionTrace.stepOk_sound model assignment hontology
    (by simp) (by simp) evidence.source_step_valid

structure DecodedLiveFactorEvidence where
  sourceClauseId : Nat
  source : FCL
  commonTerm : FTerm
  firstTerm : FTerm
  secondTerm : FTerm
  result : FCL
  step_valid : CBProductionTrace.stepOk [] [] [source] result
    (.factor 0 commonTerm firstTerm secondTerm) = true

def WireLiveRuleEvidence.decodeFactor (production : DecodedProductionRun)
    (bits : Nat) (arena : List FCL) (result : FCL)
    (wire : WireLiveRuleEvidence) : Except String DecodedLiveFactorEvidence := do
  if wire.kind != "factor" then
    throw s!"unsupported CB live Factor-evidence kind {wire.kind}"
  if wire.ontology_index.isSome ∨ wire.instantiated_source.isSome ∨
      wire.context_clause_ids.isSome ∨ wire.matched_predicates.isSome ∨
      wire.substitution.isSome ∨ wire.equality_clause_id.isSome ∨
      wire.other_clause_id.isSome ∨ wire.left.isSome ∨ wire.right.isSome ∨
      wire.literal.isSome ∨ wire.consumer_clause_id.isSome ∨
      wire.provider_clause_id.isSome ∨ wire.bridge_clause_id.isSome ∨
      wire.ground.isSome ∨ wire.general.isSome ∨ wire.term.isSome ∨
      wire.hasPredFields = true then
    throw "CB live Factor evidence carries fields from another rule"
  let sourceClauseId ← requireSome
    "CB live Factor evidence omits its source clause"
    wire.source_clause_id
  let source ← match arena[sourceClauseId]? with
    | some source => pure source
    | none => throw "CB live Factor source id is outside its context arena"
  let commonRaw ← requireSome "CB live Factor evidence omits common" wire.common
  let firstRaw ← requireSome "CB live Factor evidence omits first" wire.first
  let secondRaw ← requireSome "CB live Factor evidence omits second" wire.second
  let commonTerm ← decodeRawTerm production.bounds bits commonRaw
  let firstTerm ← decodeRawTerm production.bounds bits firstRaw
  let secondTerm ← decodeRawTerm production.bounds bits secondRaw
  if hstep : CBProductionTrace.stepOk [] [] [source] result
      (.factor 0 commonTerm firstTerm secondTerm) = true then
    return {
      sourceClauseId := sourceClauseId
      source := source
      commonTerm := commonTerm
      firstTerm := firstTerm
      secondTerm := secondTerm
      result := result
      step_valid := hstep
    }
  else throw "CB live Factor conclusion was rejected"

theorem DecodedLiveFactorEvidence.sound
    (evidence : DecodedLiveFactorEvidence)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hsource : CBProductionTrace.HoldsAt model assignment evidence.source) :
    CBProductionTrace.HoldsAt model assignment evidence.result := by
  exact CBProductionTrace.stepOk_sound model assignment
    (by simp) (by simp)
    (by
      intro derived hderived
      simp only [List.mem_singleton] at hderived
      subst derived
      exact hsource)
    evidence.step_valid

structure DecodedLiveParamodulateEvidence where
  equalityClauseId : Nat
  equalityClause : FCL
  otherClauseId : Nat
  otherClause : FCL
  leftTerm : FTerm
  rightTerm : FTerm
  literal : FLit
  result : FCL
  trace : List CBProductionTrace.Entry
  final : List FCL
  trace_valid : CBProductionTrace.checkFold [] [] [equalityClause, otherClause]
    trace = some final
  result_derived : result ∈ final

def WireLiveRuleEvidence.decodeParamodulate (production : DecodedProductionRun)
    (bits : Nat) (arena : List FCL) (result : FCL)
    (wire : WireLiveRuleEvidence) : Except String DecodedLiveParamodulateEvidence := do
  if wire.kind != "paramodulate" then
    throw s!"unsupported CB live paramodulation-evidence kind {wire.kind}"
  if wire.ontology_index.isSome ∨ wire.instantiated_source.isSome ∨
      wire.context_clause_ids.isSome ∨ wire.matched_predicates.isSome ∨
      wire.substitution.isSome ∨ wire.source_clause_id.isSome ∨
      wire.common.isSome ∨ wire.first.isSome ∨ wire.second.isSome ∨
      wire.consumer_clause_id.isSome ∨ wire.provider_clause_id.isSome ∨
      wire.bridge_clause_id.isSome ∨ wire.ground.isSome ∨
      wire.general.isSome ∨ wire.term.isSome ∨ wire.hasPredFields = true then
    throw "CB live paramodulation evidence carries fields from another rule"
  let equalityClauseId ← requireSome
    "CB live paramodulation evidence omits its equality clause"
    wire.equality_clause_id
  let equalityClause ← match arena[equalityClauseId]? with
    | some clause => pure clause
    | none => throw "CB live paramodulation equality id is outside its context arena"
  let otherClauseId ← requireSome
    "CB live paramodulation evidence omits its other clause"
    wire.other_clause_id
  let otherClause ← match arena[otherClauseId]? with
    | some clause => pure clause
    | none => throw "CB live paramodulation other id is outside its context arena"
  let leftRaw ← requireSome "CB live paramodulation evidence omits left" wire.left
  let rightRaw ← requireSome "CB live paramodulation evidence omits right" wire.right
  let literalWire ← requireSome
    "CB live paramodulation evidence omits its rewritten literal" wire.literal
  let leftTerm ← decodeRawTerm production.bounds bits leftRaw
  let rightTerm ← decodeRawTerm production.bounds bits rightRaw
  let literal ← literalWire.decode production.bounds bits
  let directTrace : List CBProductionTrace.Entry :=
    [(result, .paramodulate 0 1 leftTerm rightTerm literal)]
  match hdirect : CBProductionTrace.checkFold [] []
      [equalityClause, otherClause] directTrace with
  | some final =>
    if hresult : result ∈ final then
      return {
        equalityClauseId
        equalityClause
        otherClauseId
        otherClause
        leftTerm
        rightTerm
        literal
        result
        trace := directTrace
        final
        trace_valid := hdirect
        result_derived := hresult
      }
    else throw "CB live direct paramodulation did not derive its event clause"
  | none =>
    let intermediate := paraResolvent equalityClause otherClause
      leftTerm rightTerm literal
    let filteredTrace : List CBProductionTrace.Entry :=
      [ (intermediate, .paramodulate 0 1 leftTerm rightTerm literal)
      , (result, .deleteReflexiveInequality 2 rightTerm) ]
    match hfiltered : CBProductionTrace.checkFold [] []
        [equalityClause, otherClause] filteredTrace with
    | some final =>
      if hresult : result ∈ final then
        return {
          equalityClauseId
          equalityClause
          otherClauseId
          otherClause
          leftTerm
          rightTerm
          literal
          result
          trace := filteredTrace
          final
          trace_valid := hfiltered
          result_derived := hresult
        }
      else throw "CB live filtered paramodulation did not derive its event clause"
    | none => throw "CB live paramodulation conclusion was rejected"

theorem DecodedLiveParamodulateEvidence.sound
    (evidence : DecodedLiveParamodulateEvidence)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hequality : CBProductionTrace.HoldsAt model assignment evidence.equalityClause)
    (hother : CBProductionTrace.HoldsAt model assignment evidence.otherClause) :
    CBProductionTrace.HoldsAt model assignment evidence.result := by
  have hfinal := CBProductionTrace.checkFold_sound model assignment
    (by simp) (by simp)
    (by
      intro derived hderived
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hderived
      rcases hderived with hderived | hderived
      · simpa [hderived] using hequality
      · simpa [hderived] using hother)
    evidence.trace_valid
  exact hfinal evidence.result evidence.result_derived

structure DecodedLiveJoinResolveEvidence where
  consumerClauseId : Nat
  consumerClause : FCL
  providerClauseId : Nat
  providerClause : FCL
  literal : FLit
  result : FCL
  step_valid : CBProductionTrace.stepOk [] [] [providerClause, consumerClause] result
    (.resolve 0 1 literal) = true

def WireLiveRuleEvidence.decodeJoinResolve (production : DecodedProductionRun)
    (bits : Nat) (arena : List FCL) (result : FCL)
    (wire : WireLiveRuleEvidence) : Except String DecodedLiveJoinResolveEvidence := do
  if wire.kind != "join_resolve" then
    throw s!"unsupported CB live Join-resolution evidence kind {wire.kind}"
  if wire.ontology_index.isSome ∨ wire.instantiated_source.isSome ∨
      wire.context_clause_ids.isSome ∨ wire.matched_predicates.isSome ∨
      wire.substitution.isSome ∨ wire.source_clause_id.isSome ∨
      wire.common.isSome ∨ wire.first.isSome ∨ wire.second.isSome ∨
      wire.equality_clause_id.isSome ∨ wire.other_clause_id.isSome ∨
      wire.left.isSome ∨ wire.right.isSome ∨ wire.literal.isSome ∨
      wire.bridge_clause_id.isSome ∨ wire.general.isSome ∨ wire.term.isSome ∨
      wire.hasPredFields = true then
    throw "CB live Join resolution carries fields from another rule"
  let consumerClauseId ← requireSome
    "CB live Join resolution omits its consumer clause" wire.consumer_clause_id
  let consumerClause ← match arena[consumerClauseId]? with
    | some clause => pure clause
    | none => throw "CB live Join consumer id is outside its context arena"
  let providerClauseId ← requireSome
    "CB live Join resolution omits its provider clause" wire.provider_clause_id
  let providerClause ← match arena[providerClauseId]? with
    | some clause => pure clause
    | none => throw "CB live Join provider id is outside its context arena"
  let literalWire ← requireSome
    "CB live Join resolution omits its literal" wire.ground
  let predicate ← literalWire.decode production.bounds bits
  let literal := FLit.P predicate
  if hstep : CBProductionTrace.stepOk [] [] [providerClause, consumerClause] result
      (.resolve 0 1 literal) = true then
    return {
      consumerClauseId
      consumerClause
      providerClauseId
      providerClause
      literal
      result
      step_valid := hstep
    }
  else throw "CB live Join-resolution conclusion was rejected"

theorem DecodedLiveJoinResolveEvidence.sound
    (evidence : DecodedLiveJoinResolveEvidence)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hprovider : CBProductionTrace.HoldsAt model assignment evidence.providerClause)
    (hconsumer : CBProductionTrace.HoldsAt model assignment evidence.consumerClause) :
    CBProductionTrace.HoldsAt model assignment evidence.result := by
  exact CBProductionTrace.stepOk_sound model assignment
    (by simp) (by simp)
    (by
      intro derived hderived
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hderived
      rcases hderived with hderived | hderived
      · simpa [hderived] using hprovider
      · simpa [hderived] using hconsumer)
    evidence.step_valid

structure DecodedLiveJoin3Evidence where
  consumerClauseId : Nat
  consumerClause : FCL
  providerClauseId : Nat
  providerClause : FCL
  bridgeClauseId : Nat
  bridgeClause : FCL
  ground : FLit
  general : FLit
  term : FTerm
  result : FCL
  step_valid : CBProductionTrace.stepOk [] []
    [consumerClause, providerClause, bridgeClause] result
    (.join3 0 1 2 ground general term) = true

def WireLiveRuleEvidence.decodeJoin3 (production : DecodedProductionRun)
    (bits : Nat) (arena : List FCL) (result : FCL)
    (wire : WireLiveRuleEvidence) : Except String DecodedLiveJoin3Evidence := do
  if wire.kind != "join3" then
    throw s!"unsupported CB live Join-3 evidence kind {wire.kind}"
  if wire.ontology_index.isSome ∨ wire.instantiated_source.isSome ∨
      wire.context_clause_ids.isSome ∨ wire.matched_predicates.isSome ∨
      wire.substitution.isSome ∨ wire.source_clause_id.isSome ∨
      wire.common.isSome ∨ wire.first.isSome ∨ wire.second.isSome ∨
      wire.equality_clause_id.isSome ∨ wire.other_clause_id.isSome ∨
      wire.left.isSome ∨ wire.right.isSome ∨ wire.literal.isSome ∨
      wire.hasPredFields = true then
    throw "CB live Join-3 evidence carries fields from another rule"
  let consumerClauseId ← requireSome
    "CB live Join-3 omits its consumer clause" wire.consumer_clause_id
  let consumerClause ← match arena[consumerClauseId]? with
    | some clause => pure clause
    | none => throw "CB live Join-3 consumer id is outside its context arena"
  let providerClauseId ← requireSome
    "CB live Join-3 omits its provider clause" wire.provider_clause_id
  let providerClause ← match arena[providerClauseId]? with
    | some clause => pure clause
    | none => throw "CB live Join-3 provider id is outside its context arena"
  let bridgeClauseId ← requireSome
    "CB live Join-3 omits its bridge clause" wire.bridge_clause_id
  let bridgeClause ← match arena[bridgeClauseId]? with
    | some clause => pure clause
    | none => throw "CB live Join-3 bridge id is outside its context arena"
  let groundWire ← requireSome "CB live Join-3 omits ground" wire.ground
  let generalWire ← requireSome "CB live Join-3 omits general" wire.general
  let termRaw ← requireSome "CB live Join-3 omits its term" wire.term
  let ground := FLit.P (← groundWire.decode production.bounds bits)
  let general := FLit.P (← generalWire.decode production.bounds bits)
  let term ← decodeRawTerm production.bounds bits termRaw
  if hstep : CBProductionTrace.stepOk [] []
      [consumerClause, providerClause, bridgeClause] result
      (.join3 0 1 2 ground general term) = true then
    return {
      consumerClauseId
      consumerClause
      providerClauseId
      providerClause
      bridgeClauseId
      bridgeClause
      ground
      general
      term
      result
      step_valid := hstep
    }
  else throw "CB live Join-3 conclusion was rejected"

theorem DecodedLiveJoin3Evidence.sound
    (evidence : DecodedLiveJoin3Evidence)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hconsumer : CBProductionTrace.HoldsAt model assignment evidence.consumerClause)
    (hprovider : CBProductionTrace.HoldsAt model assignment evidence.providerClause)
    (hbridge : CBProductionTrace.HoldsAt model assignment evidence.bridgeClause) :
    CBProductionTrace.HoldsAt model assignment evidence.result := by
  exact CBProductionTrace.stepOk_sound model assignment
    (by simp) (by simp)
    (by
      intro derived hderived
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hderived
      rcases hderived with hderived | hderived
      · simpa [hderived] using hconsumer
      · rcases hderived with hderived | hderived
        · simpa [hderived] using hprovider
        · simpa [hderived] using hbridge)
    evidence.step_valid

structure DecodedLivePredProvider where
  clauseId : Nat
  clause : FCL
  matched : FPred
  matched_in_head : FLit.P matched ∈ clause.head

def livePredConclusion : FCL → List DecodedLivePredProvider → FCL
  | current, [] => current
  | current, provider :: rest =>
      livePredConclusion (resolvent provider.clause current (.P provider.matched)) rest

def livePredStepsOk : FCL → List DecodedLivePredProvider → Bool
  | _, [] => true
  | current, provider :: rest =>
      decide (FLit.P provider.matched ∈ provider.clause.head) &&
      decide (FLit.P provider.matched ∈ current.body) &&
      livePredStepsOk
        (resolvent provider.clause current (.P provider.matched)) rest

def decodeLivePredProviders (bounds : Bounds) (bits : Nat) (arena : List FCL) :
    List Nat → List WireLivePredicate → Except String (List DecodedLivePredProvider)
  | [], [] => pure []
  | clauseId :: clauseIds, wirePredicate :: wirePredicates => do
      let clause ← match arena[clauseId]? with
        | some clause => pure clause
        | none => throw "CB live Pred provider id is outside its receiver arena"
      let matched ← wirePredicate.decode bounds bits
      if hmatched : FLit.P matched ∈ clause.head then
        return { clauseId, clause, matched, matched_in_head := hmatched } ::
          (← decodeLivePredProviders bounds bits arena clauseIds wirePredicates)
      else throw "CB live Pred matched predicate is absent from its provider head"
  | _, _ => throw "CB live Pred provider and matched-predicate lengths differ"

def predBackwardSubstitution (edgeLabel : FTerm) : List (Int × FTerm) :=
  let parent := match edgeLabel with
    | .app _ argument => argument
    | _ => .var 0
  [(-1, parent), (0, edgeLabel)]

structure DecodedLivePredEvidence (production : DecodedProductionRun) where
  senderIndex : Fin production.contexts.length
  senderClauseId : Nat
  senderClause : FCL
  edgeLabel : FTerm
  payload : FCL
  payload_equiv : clEquivT payload
    (CBInterContext.predTransfer (predBackwardSubstitution edgeLabel)
      (production.contexts.get senderIndex).core senderClause)
  providers : List DecodedLivePredProvider
  steps_ok : livePredStepsOk payload providers = true
  result : FCL
  result_equiv : clEquivT result (livePredConclusion payload providers)

def WireLiveRuleEvidence.decodePred (production : DecodedProductionRun)
    (bits : Nat) (ordinary root receiverArena : List FCL) (result : FCL)
    (wire : WireLiveRuleEvidence) : Except String (DecodedLivePredEvidence production) := do
  if wire.kind != "pred" then
    throw s!"unsupported CB live Pred evidence kind {wire.kind}"
  let senderIndexRaw ← requireSome
    "CB live Pred evidence omits its sender context" wire.sender_context_index
  if hsender : senderIndexRaw < production.contexts.length then
    let senderIndex : Fin production.contexts.length := ⟨senderIndexRaw, hsender⟩
    let sender := production.contexts.get senderIndex
    let senderArena := if sender.root then root else ordinary
    let senderClauseId ← requireSome
      "CB live Pred evidence omits its sender clause" wire.sender_clause_id
    let senderClause ← match senderArena[senderClauseId]? with
      | some clause => pure clause
      | none => throw "CB live Pred sender clause id is outside its arena"
    let edgeLabelRaw ← requireSome
      "CB live Pred evidence omits its edge label" wire.edge_label
    let edgeLabel ← decodeRawTerm production.bounds bits edgeLabelRaw
    let payloadWire ← requireSome "CB live Pred evidence omits its payload" wire.payload
    let payload ← payloadWire.decode production.bounds bits
    let expectedPayload := CBInterContext.predTransfer
      (predBackwardSubstitution edgeLabel) sender.core senderClause
    if hpayload : clEquivT payload expectedPayload then
      let providerIds ← requireSome
        "CB live Pred evidence omits its provider clauses" wire.provider_clause_ids
      let matchedWires ← requireSome
        "CB live Pred evidence omits its matched predicates" wire.matched_predicates
      let providers ← decodeLivePredProviders production.bounds bits receiverArena
        providerIds matchedWires
      if hsteps : livePredStepsOk payload providers = true then
        let expectedResult := livePredConclusion payload providers
        if hresult : clEquivT result expectedResult then
          return {
            senderIndex
            senderClauseId
            senderClause
            edgeLabel
            payload
            payload_equiv := hpayload
            providers
            steps_ok := hsteps
            result
            result_equiv := hresult
          }
        else throw "CB live Pred result differs from its checked resolution fold"
      else throw "CB live Pred provider does not discharge the current payload body"
    else throw "CB live Pred payload differs from its sender transfer"
  else throw "CB live Pred sender context is outside the production run"

theorem livePredConclusion_contextValid
    (receiverCore : List FPred) (providers : List DecodedLivePredProvider)
    {D : Type} (model : TModel D) (current : FCL)
    (hcurrent : CBInterContext.ContextValid model receiverCore current)
    (hproviders : ∀ provider ∈ providers,
      CBInterContext.ContextValid model receiverCore provider.clause)
    (hsteps : livePredStepsOk current providers = true) :
    CBInterContext.ContextValid model receiverCore
      (livePredConclusion current providers) := by
  induction providers generalizing current with
  | nil => exact hcurrent
  | cons provider rest ih =>
      simp only [livePredStepsOk, Bool.and_eq_true] at hsteps
      have hresolved := CBInterContext.resolveContextual_sound model receiverCore
        provider.clause current (.P provider.matched)
        (hproviders provider (by simp)) hcurrent
        (of_decide_eq_true hsteps.1.1) (of_decide_eq_true hsteps.1.2)
      exact ih _ hresolved (by
        intro candidate hcandidate
        exact hproviders candidate (by simp [hcandidate])) hsteps.2

theorem DecodedLivePredEvidence.result_contextValid
    (evidence : DecodedLivePredEvidence production)
    (receiverCore : List FPred)
    {D : Type} (model : TModel D)
    (hsender : CBInterContext.ContextValid model
      (production.contexts.get evidence.senderIndex).core evidence.senderClause)
    (hproviders : ∀ provider ∈ evidence.providers,
      CBInterContext.ContextValid model receiverCore provider.clause) :
    CBInterContext.ContextValid model receiverCore evidence.result := by
  have hpayloadExpected := CBInterContext.predTransfer_sound model
    (production.contexts.get evidence.senderIndex).core evidence.senderClause
    (predBackwardSubstitution evidence.edgeLabel) hsender
  have hpayload : valid model evidence.payload := by
    intro assignment
    exact sat_of_clEquivT evidence.payload_equiv (hpayloadExpected assignment)
  have hfold := livePredConclusion_contextValid receiverCore evidence.providers model
    evidence.payload (by intro assignment _; exact hpayload assignment)
    hproviders evidence.steps_ok
  intro assignment hcore
  exact sat_of_clEquivT evidence.result_equiv (hfold assignment hcore)

def terminalOfGlobal (global : DecodedCBGlobalModelDocument) :=
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

inductive LiveInsertionOrigin where
  | core (index : Nat)
  | ontologyFact (index : Nat)
  | derived
deriving Repr, DecidableEq

private def liveAssumptionClause (predicate : FPred) : FCL :=
  ⟨[], [.P predicate]⟩

private def insertionOriginOk (production : DecodedProductionRun)
    (contextIndex : Fin production.contexts.length) (clause : FCL) :
    LiveInsertionOrigin → Bool
  | .core index =>
      match (production.contexts.get contextIndex).core[index]? with
      | some predicate => decide (clause = liveAssumptionClause predicate)
      | none => false
  | .ontologyFact index =>
      match production.source.ontology[index]? with
      | some source => decide (source.body = [] ∧ clause = source)
      | none => false
  | .derived => true

structure DecodedLiveInsertionEvent (production : DecodedProductionRun)
    (ordinary root : List FCL) where
  sequence : Nat
  contextIndex : Fin production.contexts.length
  rootDomain : Bool
  root_eq : (production.contexts.get contextIndex).root = rootDomain
  clauseId : Nat
  clause : FCL
  origin : LiveInsertionOrigin
  origin_valid : insertionOriginOk production contextIndex clause origin = true
  ruleHint : Option String
  hyperEvidence : Option (DecodedLiveHyperEvidence production)
  factorEvidence : Option DecodedLiveFactorEvidence
  paramodulateEvidence : Option DecodedLiveParamodulateEvidence
  joinResolveEvidence : Option DecodedLiveJoinResolveEvidence
  join3Evidence : Option DecodedLiveJoin3Evidence
  predEvidence : Option (DecodedLivePredEvidence production)

def WireLiveInsertionEvent.decode (production : DecodedProductionRun)
    (bits : Nat) (ordinary root : List FCL) (wire : WireLiveInsertionEvent) :
    Except String (DecodedLiveInsertionEvent production ordinary root) := do
  if hcontext : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length := ⟨wire.context_index, hcontext⟩
    let context := production.contexts.get contextIndex
    if hroot : context.root = wire.root then
      let arena := if wire.root then root else ordinary
      match arena[wire.clause_id]? with
      | some clause =>
          let origin ← match wire.origin_hint, wire.origin_index with
            | "core", some index => pure (.core index)
            | "ontology_fact", some index => pure (.ontologyFact index)
            | "derived", none => pure .derived
            | "core", none => throw "CB core insertion origin has no index"
            | "ontology_fact", none =>
                throw "CB ontology-fact insertion origin has no index"
            | "derived", some _ =>
                throw "CB derived insertion origin unexpectedly has an index"
            | hint, _ => throw s!"unsupported CB insertion origin {hint}"
          if horigin : insertionOriginOk production contextIndex clause origin = true then
            let (hyperEvidence, factorEvidence, paramodulateEvidence,
                joinResolveEvidence, join3Evidence, predEvidence) ←
              match origin, wire.rule_hint, wire.rule_evidence with
              | LiveInsertionOrigin.core _, none, none =>
                  pure (none, none, none, none, none, none)
              | LiveInsertionOrigin.ontologyFact _, none, none =>
                  pure (none, none, none, none, none, none)
              | LiveInsertionOrigin.derived, some "hyper", some evidence =>
                  let decoded ← evidence.decodeHyper production bits arena
                  pure (some decoded, none, none, none, none, none)
              | LiveInsertionOrigin.derived, some "factor", some evidence =>
                  let decoded ← evidence.decodeFactor production bits arena clause
                  pure (none, some decoded, none, none, none, none)
              | LiveInsertionOrigin.derived, some "eq", some evidence =>
                  let decoded ← evidence.decodeParamodulate production bits arena clause
                  pure (none, none, some decoded, none, none, none)
              | LiveInsertionOrigin.derived, some "join", some evidence =>
                  if evidence.kind = "join_resolve" then
                    let decoded ← evidence.decodeJoinResolve production bits arena clause
                    pure (none, none, none, some decoded, none, none)
                  else if evidence.kind = "join3" then
                    let decoded ← evidence.decodeJoin3 production bits arena clause
                    pure (none, none, none, none, some decoded, none)
                  else throw s!"unsupported CB live Join-evidence kind {evidence.kind}"
              | LiveInsertionOrigin.derived, some hint, some evidence =>
                  if hint = "pred-local" ∨ hint = "pred-arrival" then
                    let decoded ← evidence.decodePred production bits ordinary root arena clause
                    pure (none, none, none, none, none, some decoded)
                  else throw s!"unsupported CB live evidence for rule {hint}"
              | LiveInsertionOrigin.derived, some hint, none =>
                  if ["pred-local", "pred-arrival", "succ", "eq", "join",
                      "filtered-seed"].contains hint then
                    pure (none, none, none, none, none, none)
                  else throw s!"unsupported CB live derived-rule hint {hint}"
              | LiveInsertionOrigin.core _, _, _ |
                  LiveInsertionOrigin.ontologyFact _, _, _ =>
                  throw "CB live insertion seed unexpectedly carries rule metadata"
              | LiveInsertionOrigin.derived, none, _ =>
                  throw "CB live derived insertion omits its rule hint"
            return {
              sequence := wire.sequence
              contextIndex := contextIndex
              rootDomain := wire.root
              root_eq := hroot
              clauseId := wire.clause_id
              clause := clause
              origin := origin
              origin_valid := horigin
              ruleHint := wire.rule_hint
              hyperEvidence
              factorEvidence
              paramodulateEvidence
              joinResolveEvidence
              join3Evidence
              predEvidence
            }
          else throw "CB insertion origin does not match its indexed production seed"
      | none => throw "CB insertion-history clause id is outside its arena"
    else throw "CB insertion-history arena domain differs from its context"
  else throw "CB insertion-history context is outside the production run"

theorem DecodedLiveInsertionEvent.core_origin_exact
    (event : DecodedLiveInsertionEvent production ordinary root)
    (index : Nat) (horigin : event.origin = .core index) :
    ∃ predicate,
      (production.contexts.get event.contextIndex).core[index]? = some predicate ∧
      event.clause = liveAssumptionClause predicate := by
  have hvalid := event.origin_valid
  rw [horigin] at hvalid
  let core := (production.contexts.get event.contextIndex).core
  change (match core[index]? with
    | some predicate => decide (event.clause = liveAssumptionClause predicate)
    | none => false) = true at hvalid
  cases hlookup : core[index]? with
  | none => simp [hlookup] at hvalid
  | some predicate =>
      have heq : event.clause = liveAssumptionClause predicate := by
        exact of_decide_eq_true (by simpa [hlookup] using hvalid)
      exact ⟨predicate, by simpa [core] using hlookup, heq⟩

theorem DecodedLiveInsertionEvent.ontology_origin_exact
    (event : DecodedLiveInsertionEvent production ordinary root)
    (index : Nat) (horigin : event.origin = .ontologyFact index) :
    ∃ source,
      production.source.ontology[index]? = some source ∧
      source.body = [] ∧ event.clause = source := by
  have hvalid := event.origin_valid
  rw [horigin] at hvalid
  let ontology := production.source.ontology
  change (match ontology[index]? with
    | some source => decide (source.body = [] ∧ event.clause = source)
    | none => false) = true at hvalid
  cases hlookup : ontology[index]? with
  | none => simp [hlookup] at hvalid
  | some source =>
      have heq : source.body = [] ∧ event.clause = source := by
        exact of_decide_eq_true (by simpa [hlookup] using hvalid)
      exact ⟨source, by simpa [ontology] using hlookup, heq⟩

theorem DecodedLiveInsertionEvent.seed_sound
    (event : DecodedLiveInsertionEvent production ordinary root)
    {D : Type} (model : TModel D) (assignment : Int → D)
    (hontology : ∀ source ∈ production.source.ontology, valid model source)
    (hcore : CoreHolds model assignment
      (production.contexts.get event.contextIndex).core)
    (hseed : event.origin ≠ .derived) :
    CBProductionTrace.HoldsAt model assignment event.clause := by
  cases horigin : event.origin with
  | core index =>
      obtain ⟨predicate, hlookup, hclause⟩ := event.core_origin_exact index horigin
      rw [hclause]
      intro _
      exact ⟨.P predicate, List.mem_singleton.mpr rfl,
        hcore predicate (List.mem_of_getElem? hlookup)⟩
  | ontologyFact index =>
      obtain ⟨source, hlookup, _, hclause⟩ :=
        event.ontology_origin_exact index horigin
      rw [hclause]
      exact hontology source (List.mem_of_getElem? hlookup) assignment
  | derived => exact (hseed horigin).elim

structure DecodedLiveContext
    (production : DecodedProductionRun)
    (terminal : ContextCalculus.CBTerminalStateWire.DecodedCBTerminalStateDocument)
    (ordinary root : List FCL) where
  contextIndex : Fin production.contexts.length
  contextId : Nat
  rootDomain : Bool
  live : WireLiveContext
  context_id_eq : (production.contexts.get contextIndex).contextId = contextId
  root_eq : (production.contexts.get contextIndex).root = rootDomain
  nominal_ground_eq : (production.contexts.get contextIndex).nominalGround =
    live.nominal_ground
  query_concept_eq : (production.contexts.get contextIndex).queryConcept =
    live.query_concept
  core : List FPred
  core_eq : core = (production.contexts.get contextIndex).core
  retainedClauseIds : List Nat
  retained : List FCL
  retained_eq : retained = (production.contexts.get contextIndex).retained
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
  contexts.all fun context => context.retained.all fun clause =>
    history.any fun event =>
      decide (event.contextIndex = context.contextIndex) &&
        decide (event.clause = clause)

def WireLiveContext.decode (production : DecodedProductionRun)
    (terminal : ContextCalculus.CBTerminalStateWire.DecodedCBTerminalStateDocument)
    (bits : Nat) (ordinary root : List FCL) (wire : WireLiveContext) :
    Except String (DecodedLiveContext production terminal ordinary root) := do
  if hindex : wire.context_index < production.contexts.length then
    let contextIndex : Fin production.contexts.length := ⟨wire.context_index, hindex⟩
    let context := production.contexts.get contextIndex
    if hid : context.contextId = wire.context_id then
      if hroot : context.root = wire.root then
        if hnominal : context.nominalGround = wire.nominal_ground then
        if hquery : context.queryConcept = wire.query_concept then
        let core ← wire.core.mapM
          (WireLivePredicate.decode production.bounds bits)
        if hcore : core = context.core then
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
              return DecodedLiveContext.mk contextIndex wire.context_id wire.root wire
                hid hroot hnominal hquery core hcore wire.retained_clause_ids retained hretained predecessors
                hpredecessors successors hsuccessors hpredWatermarks hsuccWatermarks
                hterminalLength hterminal
            else throw "CB live queues or high-water marks differ from terminal evidence"
          else throw "CB live and terminal-evidence context counts differ"
          else throw "CB live successor watermarks differ from successor records"
          else throw "CB live predecessor watermarks differ from predecessor records"
          else throw "CB live successors differ from certified outgoing edges"
          else throw "CB live predecessors differ from certified incoming edges"
        else throw "CB live retained clauses differ from the certified terminal context"
        else throw "CB live context core differs from the certified context"
        else throw "CB live query concept differs from the certified context"
        else throw "CB live nominal-ground identity differs from the certified context"
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
  if wire.live_state.version != 6 then
    throw s!"unsupported CB live-state version {wire.live_state.version}"
  let global ← wire.global_model.decode
  let production := rProduction global.global.rsucc
  let terminal := terminalOfGlobal global
  if wire.live_state.concept_count = production.bounds.concepts then pure ()
    else throw "CB live concept bound differs from the certified production run"
  if wire.live_state.role_count = production.bounds.roles then pure ()
    else throw "CB live role bound differs from the certified production run"
  if wire.live_state.function_count = production.bounds.functions then pure ()
    else throw "CB live function bound differs from the certified production run"
  if wire.live_state.source_individual_count = production.source.bounds.individuals then pure ()
    else throw "CB live source-individual bound differs from the certified source"
  if wire.live_state.runtime_individual_count = production.bounds.individuals then pure ()
    else throw "CB live runtime-individual bound differs from the certified production run"
  let sourceOntology ← wire.live_state.source_ontology.mapM
    (WireLiveClause.decode production.source.bounds wire.live_state.comp_ind_bits)
  if sourceOntology = production.source.ontology then pure ()
    else throw "CB live normalized ontology differs from the certified source ontology"
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
      (WireLiveInsertionEvent.decode production wire.live_state.comp_ind_bits ordinary root)
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

theorem DecodedLiveStateDocument.retained_has_event
    (decoded : DecodedLiveStateDocument)
    (context : DecodedLiveContext (rProduction decoded.global.global.rsucc)
      (terminalOfGlobal decoded.global) decoded.ordinaryArena decoded.rootArena)
    (hcontext : context ∈ decoded.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained) :
    ∃ event ∈ decoded.insertionHistory,
      event.contextIndex = context.contextIndex ∧ event.clause = clause := by
  have hcontextCovered :=
    (List.all_eq_true.mp decoded.retained_insertions_present) context hcontext
  have hclauseCovered :=
    (List.all_eq_true.mp hcontextCovered) clause hclause
  simpa only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] using
    hclauseCovered

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
#print axioms DecodedLiveInsertionEvent.seed_sound
#print axioms DecodedLiveHyperEvidence.source_sound
#print axioms DecodedLiveFactorEvidence.sound
#print axioms DecodedLiveParamodulateEvidence.sound
#print axioms DecodedLiveJoinResolveEvidence.sound
#print axioms DecodedLiveJoin3Evidence.sound
#print axioms DecodedLivePredEvidence.result_contextValid

end ContextCalculus.CBLiveStateWire
