import ContextCalculus.CBSourceJoin3Closure
import ContextCalculus.CBRSuccClosure

/-!
# Source-bound Succ and r-Succ closure

Lean reconstructs direct Succ offers and the complete r-Succ
`successor-edge × reach-fact` product from the terminal source-bound snapshot.
Each offer must occur on the target's reverse predecessor edge and its
tautological hypothesis must have a retained strengthening at that target.
-/

namespace ContextCalculus.CBSourceSuccClosure

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBInterContext
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceJoin3Closure
open ContextCalculus.CBSuccClosure
open ContextCalculus.CBRSuccClosure

def isReachConcept (reachConcepts : List Nat) : FPred → Bool
  | .concept concept _ => concept ∈ reachConcepts
  | _ => false

def offerAt? (order : DecodedSourceFiniteOrder production)
    (rsuccEnabled : Bool) (reachConcepts : List Nat) (root : Bool)
    (retained : List FCL) (clauseIndex headIndex : Nat) : Option Offer := do
  let clause ← retained[clauseIndex]?
  if headIndex ∈ order.maximalHeadIndices root clause.head then pure () else none
  let .P predicate ← clause.head[headIndex]? | none
  match ordinaryEdge predicate with
  | some (edge, parent) =>
      if !rsuccEnabled && isReachConcept reachConcepts predicate then none
      else some { edge, pushed := forwardPredicate edge parent predicate }
  | none =>
      match rootForm predicate with
      | some (pushed, edge) => some { edge, pushed }
      | none => none

def directOffers (order : DecodedSourceFiniteOrder production)
    (rsuccEnabled : Bool) (reachConcepts : List Nat) (root : Bool)
    (retained : List FCL) : List Offer :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices root clause.head).filterMap fun headIndex =>
        offerAt? order rsuccEnabled reachConcepts root retained
          clauseIndex headIndex).eraseDups

def edgeDelivered
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (senderIndex targetIndex : Nat) (edge : FTerm) (pushed : FPred) : Bool :=
  match live.contexts.find? fun context =>
      context.contextIndex.val = targetIndex with
  | none => false
  | some target => target.predecessors.any fun predecessor =>
      predecessor.predecessorIndex.val = senderIndex &&
        predecessor.label = edge && pushed ∈ predecessor.pushed

def targetStrengthens
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (targetIndex : Nat) (pushed : FPred) : Bool :=
  match live.contexts.find? fun context =>
      context.contextIndex.val = targetIndex with
  | none => false
  | some target => target.retained.any fun clause =>
      decide (Strengthens clause (succHypothesis pushed))

def offerDelivered
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (senderIndex : Nat) (offer : Offer) : Bool :=
  live.contexts.any fun target =>
    edgeDelivered live senderIndex target.contextIndex.val offer.edge offer.pushed &&
      targetStrengthens live target.contextIndex.val offer.pushed

def directSuccClosedB
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (order : DecodedSourceFiniteOrder live.production)
    (rsuccEnabled : Bool) (reachConcepts : List Nat)
    (context : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) : Bool :=
  (directOffers order rsuccEnabled reachConcepts context.rootDomain
    context.retained).all fun offer =>
      offerDelivered live context.contextIndex.val offer

theorem directSuccClosedB_sound
    (order : DecodedSourceFiniteOrder live.production)
    (rsuccEnabled : Bool) (reachConcepts : List Nat)
    (context : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena)
    (hclosed : directSuccClosedB live order rsuccEnabled
      reachConcepts context = true) :
    ∀ offer ∈ directOffers order rsuccEnabled reachConcepts
        context.rootDomain context.retained,
      offerDelivered live context.contextIndex.val offer = true := by
  intro offer hoffer
  exact List.all_eq_true.mp hclosed offer hoffer

def sourceReachPredicates (reachConcepts : List Nat)
    (order : DecodedSourceFiniteOrder production) (root : Bool)
    (retained : List FCL) : List FPred :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices root clause.head).filterMap fun headIndex =>
        match (clause.head[headIndex]? : Option FLit) with
        | some (.P predicate) =>
            if CBRSuccClosure.isCentralReach reachConcepts predicate then
              some predicate else none
        | _ => none).eraseDups

def sourceRSuccOffers
    (reachConcepts : List Nat) (order : DecodedSourceFiniteOrder production)
    (context : DecodedSourceLiveContext production ordinary rootArena) :
    List RSuccOffer :=
  context.successors.flatMap fun edge =>
    (sourceReachPredicates reachConcepts order context.rootDomain
      context.retained).map fun predicate => {
        edge := { label := edge.label, targetIndex := edge.targetIndex.val }
        sourcePredicate := predicate
        pushed := forwardPredicate edge.label (parentOfEdge edge.label) predicate
      }

def rSuccClosedB
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (rsuccEnabled : Bool) (reachConcepts : List Nat)
    (order : DecodedSourceFiniteOrder live.production)
    (context : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) : Bool :=
  if rsuccEnabled then
    (sourceRSuccOffers reachConcepts order context).all fun offer =>
      edgeDelivered live context.contextIndex.val offer.edge.targetIndex
          offer.edge.label offer.pushed &&
        targetStrengthens live offer.edge.targetIndex offer.pushed
  else true

theorem rSuccClosedB_sound
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (rsuccEnabled : Bool) (reachConcepts : List Nat)
    (order : DecodedSourceFiniteOrder live.production)
    (context : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena)
    (hclosed : rSuccClosedB live rsuccEnabled reachConcepts order context = true)
    (henabled : rsuccEnabled = true) :
    ∀ offer ∈ sourceRSuccOffers reachConcepts order context,
      edgeDelivered live context.contextIndex.val offer.edge.targetIndex
          offer.edge.label offer.pushed = true ∧
        targetStrengthens live offer.edge.targetIndex offer.pushed = true := by
  subst rsuccEnabled
  simp only [rSuccClosedB, if_true] at hclosed
  intro offer hoffer
  have hand := List.all_eq_true.mp hclosed offer hoffer
  simpa only [Bool.and_eq_true] using hand

structure WireSourceSuccClosureDocument where
  version : Nat
  join3_closure : WireSourceJoin3ClosureDocument
  rsucc_enabled : Bool
  reach_concepts : List Nat
deriving FromJson, ToJson

structure DecodedSourceSuccClosureDocument where
  join3Closure : DecodedSourceJoin3ClosureDocument
  rsuccEnabled : Bool
  reachConcepts : List Nat
  reach_nodup : reachConcepts.Nodup
  reach_bounded : ∀ concept ∈ reachConcepts,
    concept < join3Closure.hyperClosure.localClosure.live.production.bounds.concepts
  direct_closed : ∀ context ∈
      join3Closure.hyperClosure.localClosure.live.contexts,
    directSuccClosedB join3Closure.hyperClosure.localClosure.live
      join3Closure.hyperClosure.order rsuccEnabled reachConcepts context = true
  rsucc_closed : ∀ context ∈
      join3Closure.hyperClosure.localClosure.live.contexts,
    rSuccClosedB join3Closure.hyperClosure.localClosure.live rsuccEnabled
      reachConcepts join3Closure.hyperClosure.order context = true

def WireSourceSuccClosureDocument.decode
    (wire : WireSourceSuccClosureDocument) :
    Except String DecodedSourceSuccClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound CB Succ-closure version {wire.version}"
  let join3Closure ← wire.join3_closure.decode
  let live := join3Closure.hyperClosure.localClosure.live
  if hnodup : wire.reach_concepts.Nodup then
    if hbounded : ∀ concept ∈ wire.reach_concepts,
        concept < live.production.bounds.concepts then
      if hdirect : ∀ context ∈ live.contexts,
          directSuccClosedB live join3Closure.hyperClosure.order
            wire.rsucc_enabled wire.reach_concepts context = true then
        if hrsucc : ∀ context ∈ live.contexts,
            rSuccClosedB live wire.rsucc_enabled wire.reach_concepts
              join3Closure.hyperClosure.order context = true then
          return {
            join3Closure
            rsuccEnabled := wire.rsucc_enabled
            reachConcepts := wire.reach_concepts
            reach_nodup := hnodup
            reach_bounded := hbounded
            direct_closed := hdirect
            rsucc_closed := hrsucc
          }
        else throw "source-bound CB terminal state is not r-Succ-closed"
      else throw "source-bound CB terminal state is not direct-Succ-closed"
    else throw "source-bound CB reach concept is outside the signature"
  else throw "source-bound CB reach concept list contains a duplicate"

def WireSourceSuccClosureDocument.check
    (wire : WireSourceSuccClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireSourceSuccClosureDocument.check_sound
    (wire : WireSourceSuccClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceSuccClosureDocument,
      wire.decode = .ok decoded ∧
      (∀ context ∈ decoded.join3Closure.hyperClosure.localClosure.live.contexts,
        ∀ offer ∈ directOffers decoded.join3Closure.hyperClosure.order
            decoded.rsuccEnabled decoded.reachConcepts context.rootDomain
            context.retained,
          offerDelivered decoded.join3Closure.hyperClosure.localClosure.live
            context.contextIndex.val offer = true) ∧
      (decoded.rsuccEnabled = true →
        ∀ context ∈ decoded.join3Closure.hyperClosure.localClosure.live.contexts,
          ∀ offer ∈ sourceRSuccOffers decoded.reachConcepts
              decoded.join3Closure.hyperClosure.order context,
            edgeDelivered decoded.join3Closure.hyperClosure.localClosure.live
                context.contextIndex.val offer.edge.targetIndex offer.edge.label
                offer.pushed = true ∧
              targetStrengthens
                decoded.join3Closure.hyperClosure.localClosure.live
                offer.edge.targetIndex offer.pushed = true) := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceSuccClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, ?_, ?_⟩
      · intro context hcontext
        exact directSuccClosedB_sound decoded.join3Closure.hyperClosure.order
          decoded.rsuccEnabled decoded.reachConcepts context
          (decoded.direct_closed context hcontext)
      · intro henabled context hcontext
        exact rSuccClosedB_sound
          decoded.join3Closure.hyperClosure.localClosure.live
          decoded.rsuccEnabled decoded.reachConcepts
          decoded.join3Closure.hyperClosure.order context
          (decoded.rsucc_closed context hcontext) henabled

#print axioms directSuccClosedB_sound
#print axioms rSuccClosedB_sound
#print axioms WireSourceSuccClosureDocument.check_sound

end ContextCalculus.CBSourceSuccClosure
