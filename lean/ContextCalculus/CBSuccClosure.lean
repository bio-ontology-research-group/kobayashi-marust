import ContextCalculus.CBJoin3ClosureWire

/-!
# Finite direct Succ closure for production CB

This module specifies the implementation-independent direct Succ offers.  It
covers ordinary anonymous successors and nominal/root successors.  The r-Succ
reachability cross-product is deliberately separate because it needs a checked
reach-concept table and the complete terminal successor-edge relation.
-/

namespace ContextCalculus.CBSuccClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBInterContext

/-- Replace every occurrence of one edge endpoint by the successor central
variable and its parent by the successor predecessor variable. -/
def forwardTerm (edge parent : FTerm) : FTerm → FTerm
  | term@(.var _) | term@(.const _) =>
      if term = edge then .var 0 else if term = parent then .var (-1) else term
  | term@(.app function argument) =>
      if term = edge then .var 0
      else .app function (forwardTerm edge parent argument)

def forwardPredicate (edge parent : FTerm) : FPred → FPred
  | .concept concept term => .concept concept (forwardTerm edge parent term)
  | .role role source target =>
      .role role (forwardTerm edge parent source) (forwardTerm edge parent target)

/-- The edge and parent selected by an ordinary Succ head predicate.  This is
the nested-term image of KM's `is_succ_trigger`, with reach-concept suppression
left to the checked wire metadata. -/
def ordinaryEdge : FPred → Option (FTerm × FTerm)
  | .concept _ edge@(.app _ parent) => some (edge, parent)
  | .role _ source target =>
      match source, target with
      | parent@(.var 0), edge@(.app _ edgeParent) =>
          if edgeParent = parent then some (edge, parent) else none
      | edge@(.app _ edgeParent), parent@(.var 0) =>
          if edgeParent = parent then some (edge, parent) else none
      | parent@(.const _), edge@(.app _ edgeParent) =>
          if edgeParent = parent then some (edge, parent) else none
      | edge@(.app _ edgeParent), parent@(.const _) =>
          if edgeParent = parent then some (edge, parent) else none
      | _, _ => none
  | _ => none

/-- Su^r form sent to the nominal ground context. -/
def rootForm : FPred → Option (FPred × FTerm)
  | predicate@(.concept _ individual@(.const _)) => some (predicate, individual)
  | .role role (.var 0) individual@(.const _) =>
      some (.role role (.var (-1)) individual, individual)
  | .role role individual@(.const _) (.var 0) =>
      some (.role role individual (.var (-1)), individual)
  | _ => none

structure Offer where
  edge : FTerm
  pushed : FPred
deriving DecidableEq, Repr

/-- One direct offer from a maximal retained head position. Ordinary Succ takes
precedence exactly when the predicate contains a successor edge; otherwise the
root form is considered. -/
def offerAt? (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) (clauseIndex headIndex : Nat) : Option Offer := do
  let clause ← retained[clauseIndex]?
  if headIndex ∈ order.maximalHeadIndices clause.head then pure () else none
  let .P predicate ← clause.head[headIndex]? | none
  match ordinaryEdge predicate with
  | some (edge, parent) =>
      some { edge, pushed := forwardPredicate edge parent predicate }
  | none =>
      match rootForm predicate with
      | some (pushed, edge) => some { edge, pushed }
      | none => none

/-- All direct Succ offers, deduplicated in first-firing order like
`pushed_succ`. -/
def directOffers (order : DecodedFiniteLiteralOrderDocument)
    (retained : List FCL) : List Offer :=
  ((List.range retained.length).flatMap fun clauseIndex =>
    match retained[clauseIndex]? with
    | none => []
    | some clause =>
      (order.maximalHeadIndices clause.head).filterMap fun headIndex =>
        offerAt? order retained clauseIndex headIndex).eraseDups

theorem mem_directOffers_has_origin
    (order : DecodedFiniteLiteralOrderDocument) (retained : List FCL)
    (offer : Offer) (hmember : offer ∈ directOffers order retained) :
    ∃ clauseIndex headIndex,
      offerAt? order retained clauseIndex headIndex = some offer := by
  simp only [directOffers, List.mem_eraseDups, List.mem_flatMap,
    List.mem_range] at hmember
  obtain ⟨clauseIndex, _hclauseIndex, htail⟩ := hmember
  cases hclause : retained[clauseIndex]? with
  | none => simp [hclause] at htail
  | some clause =>
      simp only [hclause, List.mem_filterMap] at htail
      obtain ⟨headIndex, _hheadIndex, horigin⟩ := htail
      exact ⟨clauseIndex, headIndex, horigin⟩

/-- Applying a direct Succ offer installs only the tautological edge hypothesis;
it introduces no model assumption. -/
theorem offer_hypothesis_valid {D : Type} (model : TModel D)
    (offer : Offer) : valid model (succHypothesis offer.pushed) :=
  succHypothesis_valid model offer.pushed

example : ordinaryEdge (.role 0 (.var 0) (.app 2 (.var 0))) =
    some (.app 2 (.var 0), .var 0) := by native_decide

#print axioms mem_directOffers_has_origin
#print axioms offer_hypothesis_valid

end ContextCalculus.CBSuccClosure
