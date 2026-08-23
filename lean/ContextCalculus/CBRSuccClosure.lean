import ContextCalculus.CBSuccClosureWire

/-!
# Finite production r-Succ closure

This module reconstructs KM's complete r-Succ cross-product from two checked
inputs: the reach-concept signature and the terminal predecessor snapshots.
The latter are the reverse representation of every live successor edge.  The
semi-naive watermarks are an implementation detail; the terminal obligation is
the same finite `outgoing edges × central reach facts` product.
-/

namespace ContextCalculus.CBRSuccClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBPredSendCoverageWire
open ContextCalculus.CBJoin3ClosureWire
open ContextCalculus.CBSuccClosure
open ContextCalculus.CBSuccClosureWire
open ContextCalculus.CBFiniteLiteralOrderWire

structure OutgoingEdge where
  label : FTerm
  targetIndex : Nat
deriving DecidableEq, Repr

/-- Reverse the exact predecessor snapshots into the outgoing successor edges
of one production context. -/
def outgoingEdges (coverage : DecodedPredSendCoverageDocument)
    (sourceIndex : Nat) : List OutgoingEdge :=
  let ordinary := coverage.senders.flatMap fun target =>
    target.edges.filterMap fun edge =>
      if edge.receiverIndex.val = sourceIndex then
        some { label := edge.label, targetIndex := target.senderIndex.val }
      else none
  let root := coverage.rootSender.toList.flatMap fun target =>
    target.edges.filterMap fun edge =>
      if edge.receiverIndex.val = sourceIndex then
        some {
          label := .const edge.individual
          targetIndex := target.senderIndex.val
        }
      else none
  (ordinary ++ root).eraseDups

def isCentralReach (reachConcepts : List Nat) : FPred → Bool
  | .concept concept (.var 0) => decide (concept ∈ reachConcepts)
  | _ => false

/-- Ordered-unique maximal central reach facts, matching `rsucc_reach_tail`
folded over the append-only terminal pool. -/
def reachPredicates (reachConcepts : List Nat)
    (order : DecodedFiniteLiteralOrderDocument) (retained : List FCL) : List FPred :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices clause.head).filterMap fun headIndex =>
        match (clause.head[headIndex]? : Option FLit) with
        | some (FLit.P predicate) =>
            if isCentralReach reachConcepts predicate then some predicate else none
        | _ => none).eraseDups

structure RSuccOffer where
  edge : OutgoingEdge
  sourcePredicate : FPred
  pushed : FPred
deriving DecidableEq, Repr

def parentOfEdge : FTerm → FTerm
  | .app _ parent => parent
  | term => term

def rSuccOffers (coverage : DecodedPredSendCoverageDocument)
    (reachConcepts : List Nat) (order : DecodedFiniteLiteralOrderDocument)
    (sourceIndex : Nat) (retained : List FCL) : List RSuccOffer :=
  (outgoingEdges coverage sourceIndex).flatMap fun edge =>
    (reachPredicates reachConcepts order retained).map fun predicate => {
      edge
      sourcePredicate := predicate
      pushed := forwardPredicate edge.label (parentOfEdge edge.label) predicate
    }

theorem mem_rSuccOffers_iff {coverage : DecodedPredSendCoverageDocument}
    {reachConcepts : List Nat} {order : DecodedFiniteLiteralOrderDocument}
    {sourceIndex : Nat} {retained : List FCL} {offer : RSuccOffer} :
    offer ∈ rSuccOffers coverage reachConcepts order sourceIndex retained ↔
      ∃ edge ∈ outgoingEdges coverage sourceIndex,
        ∃ predicate ∈ reachPredicates reachConcepts order retained,
          offer = {
            edge := edge
            sourcePredicate := predicate
            pushed := forwardPredicate edge.label (parentOfEdge edge.label) predicate
          } := by
  simp [rSuccOffers, eq_comm]

/-- Every r-Succ payload is again a tautological hypothesis at its target. -/
theorem rSuccOffer_valid {D : Type} (model : TModel D) (offer : RSuccOffer) :
    valid model (ContextCalculus.CBInterContext.succHypothesis offer.pushed) :=
  ContextCalculus.CBInterContext.succHypothesis_valid model offer.pushed

#print axioms mem_rSuccOffers_iff
#print axioms rSuccOffer_valid

end ContextCalculus.CBRSuccClosure
