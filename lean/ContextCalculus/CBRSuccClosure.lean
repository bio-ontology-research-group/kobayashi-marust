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

/-- The labels of individuals that r-Succ offers.  `concepts` is KM's
`Sig::grounded_label`.  With `everyEdge` off, a label `B(o)` goes over the
grounded successor edge `f(o)` of that individual only; the nominal ground
context holds the labels of an individual on its constant, and the successor
`f(o)` reads them as labels of its predecessor `y`.  With `everyEdge` on, a
label `B(o)` goes over every successor edge, as in the r-Succ rule of
arXiv:1805.01396 (`Su^r` contains `B(o)`): a context that derived `B(o)` under
its own hypotheses hands it to its successors, which read it on the constant
`o` (`forwardPredicate_individual_label`). -/
structure IndividualLabels where
  concepts : List Nat := []
  everyEdge : Bool := false
deriving DecidableEq, Repr

/-- Whether the edge labelled `edge` carries the label `B(o)` of an
individual (KM's `rsucc_offered_over`).  Root edges (labelled by a constant)
carry central reach facts only. -/
def isGroundedLabel (labels : IndividualLabels) (edge : FTerm) : FPred → Bool
  | .concept concept (.const individual) =>
      match edge with
      | .app _ (.const parent) =>
          decide (concept ∈ labels.concepts) && (labels.everyEdge || decide (parent = individual))
      | .app _ _ => decide (concept ∈ labels.concepts) && labels.everyEdge
      | _ => false
  | _ => false

/-- Whether the edge labelled `edge` carries the reach fact `predicate`. -/
def offeredOver (reachConcepts : List Nat) (groundedConcepts : IndividualLabels) (edge : FTerm)
    (predicate : FPred) : Bool :=
  isCentralReach reachConcepts predicate || isGroundedLabel groundedConcepts edge predicate

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

/-- Ordered-unique maximal reach facts that the edge labelled `edge`
carries: the central reach facts (`reachPredicates`) on every edge, and on a
grounded edge `f(o)` also the labels of `o`.  KM folds both kinds over one
append-only pool and filters them per edge. -/
def edgeReachPredicates (reachConcepts : List Nat) (groundedConcepts : IndividualLabels)
    (order : DecodedFiniteLiteralOrderDocument) (retained : List FCL)
    (edge : FTerm) : List FPred :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices clause.head).filterMap fun headIndex =>
        match (clause.head[headIndex]? : Option FLit) with
        | some (FLit.P predicate) =>
            if offeredOver reachConcepts groundedConcepts edge predicate then some predicate
            else none
        | _ => none).eraseDups

structure RSuccOffer where
  edge : OutgoingEdge
  sourcePredicate : FPred
  pushed : FPred
deriving DecidableEq, Repr

/-- The parent of an edge label, i.e. the term that `forwardTerm` maps to
the predecessor variable `y`: `x` for an ordinary `f(x)` edge, `o` for a
grounded `f(o)` edge, and `x` for a root edge labelled by the individual `o`
(the source context's element is the ground context's predecessor; KM's
`forwards(o, ·)` maps `x ↦ y`, docs/NOMINALS-CB.md section 12). -/
def parentOfEdge : FTerm → FTerm
  | .app _ parent => parent
  | .const _ => .var 0
  | term => term

/-- A root-edge offer of the central label `B(x)` pushes `B(y)`. -/
theorem forwardPredicate_root_label (individual concept : Nat) :
    forwardPredicate (.const individual) (parentOfEdge (.const individual))
        (.concept concept (.var 0)) =
      .concept concept (.var (-1)) := by
  simp [parentOfEdge, forwardPredicate, forwardTerm]

/-- A grounded-edge offer of the label `B(o)` pushes `B(y)`. -/
theorem forwardPredicate_grounded_label (function individual concept : Nat) :
    forwardPredicate (.app function (.const individual))
        (parentOfEdge (.app function (.const individual)))
        (.concept concept (.const individual)) =
      .concept concept (.var (-1)) := by
  simp [parentOfEdge, forwardPredicate, forwardTerm]

/-- Over an ordinary successor edge `f(t)` whose parent `t` is not the
individual `o`, an offer of the label `B(o)` keeps the constant: the
successor receives the hypothesis `B(o)`. -/
theorem forwardPredicate_individual_label (function individual concept : Nat)
    (parent : FTerm) (hparent : parent ≠ .const individual) :
    forwardPredicate (.app function parent) (parentOfEdge (.app function parent))
        (.concept concept (.const individual)) =
      .concept concept (.const individual) := by
  have h : (FTerm.const individual = parent) = False := by
    apply propext; constructor
    · intro e; exact hparent e.symm
    · intro e; exact e.elim
  simp [parentOfEdge, forwardPredicate, forwardTerm, h]

def rSuccOffers (coverage : DecodedPredSendCoverageDocument)
    (reachConcepts : List Nat) (groundedConcepts : IndividualLabels) (order : DecodedFiniteLiteralOrderDocument)
    (sourceIndex : Nat) (retained : List FCL) : List RSuccOffer :=
  (outgoingEdges coverage sourceIndex).flatMap fun edge =>
    (edgeReachPredicates reachConcepts groundedConcepts order retained edge.label).map
      fun predicate => {
      edge
      sourcePredicate := predicate
      pushed := forwardPredicate edge.label (parentOfEdge edge.label) predicate
    }

theorem mem_rSuccOffers_iff {coverage : DecodedPredSendCoverageDocument}
    {reachConcepts : List Nat} {groundedConcepts : IndividualLabels} {order : DecodedFiniteLiteralOrderDocument}
    {sourceIndex : Nat} {retained : List FCL} {offer : RSuccOffer} :
    offer ∈ rSuccOffers coverage reachConcepts groundedConcepts order sourceIndex retained ↔
      ∃ edge ∈ outgoingEdges coverage sourceIndex,
        ∃ predicate ∈ edgeReachPredicates reachConcepts groundedConcepts order retained
            edge.label,
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
#print axioms forwardPredicate_root_label
#print axioms forwardPredicate_grounded_label
#print axioms forwardPredicate_individual_label

end ContextCalculus.CBRSuccClosure
