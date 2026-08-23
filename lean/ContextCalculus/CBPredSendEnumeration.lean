import ContextCalculus.CBPredEnumeration

/-!
# Exact ordinary-Pred send enumeration

This module gives an executable, finite specification of the ordinary Pred
send loop in `engine.rs`.  It deliberately operates on a typed terminal
snapshot.  A later wire layer must prove that the snapshot is exactly KM's
retained context and predecessor-edge state.

For every retained clause and predecessor edge, the enumerator checks the two
logical production conditions: the clause has a function-free Pred-compatible
head, and every body predicate belongs to the complete pushed set of that
edge.  The membership theorem proves that the resulting key list neither omits
nor invents an eligible pair.
-/

namespace ContextCalculus.CBPredSendEnumeration

open ContextCalculus ContextCalculus.CheckerTerm

structure PredEdge where
  receiverIndex : Nat
  label : FTerm
  pushed : List FPred
deriving DecidableEq, Repr

structure SendKey where
  retainedIndex : Nat
  edgeIndex : Nat
deriving DecidableEq, Repr

def functionFreeTerm : FTerm → Bool
  | .app _ _ => false
  | .var _ | .const _ => true

def functionFreePred : FPred → Bool
  | .concept _ term => functionFreeTerm term
  | .role _ source target =>
      functionFreeTerm source && functionFreeTerm target

def predHeadLiteralEligible : FLit → Bool
  | .P predicate => functionFreePred predicate
  | .eq (.const _) (.var index) => index = 0 || index = -1
  | .eq (.const _) (.const _) => true
  | .eq _ _ | .ineq _ _ => false

def predClauseEligible (clause : FCL) : Bool :=
  clause.head.all predHeadLiteralEligible

def bodyPredicates : List FLit → Option (List FPred)
  | [] => some []
  | .P predicate :: rest =>
      (bodyPredicates rest).map (predicate :: ·)
  | _ :: _ => none

def edgeCoversBody (edge : PredEdge) (clause : FCL) : Bool :=
  match bodyPredicates clause.body with
  | none => false
  | some body => body.all fun predicate => decide (predicate ∈ edge.pushed)

def eligible (retained : List FCL) (edges : List PredEdge)
    (key : SendKey) : Bool :=
  match retained[key.retainedIndex]?, edges[key.edgeIndex]? with
  | some clause, some edge =>
      predClauseEligible clause && edgeCoversBody edge clause
  | _, _ => false

/-- Clause-major, edge-minor order, matching KM's terminal full scan. -/
def enumerate (retained : List FCL) (edges : List PredEdge) : List SendKey :=
  (List.range retained.length).flatMap fun retainedIndex =>
    (List.range edges.length).filterMap fun edgeIndex =>
      let key := { retainedIndex, edgeIndex }
      if eligible retained edges key then some key else none

theorem mem_enumerate_iff (retained : List FCL) (edges : List PredEdge)
    (key : SendKey) :
    key ∈ enumerate retained edges ↔
      key.retainedIndex < retained.length ∧
      key.edgeIndex < edges.length ∧
      eligible retained edges key = true := by
  simp only [enumerate, List.mem_flatMap, List.mem_range,
    List.mem_filterMap]
  constructor
  · rintro ⟨retainedIndex, hretained, edgeIndex, hedge, hselected⟩
    split at hselected
    next heligible =>
      simp only [Option.some.injEq] at hselected
      subst key
      exact ⟨hretained, hedge, heligible⟩
    next => simp at hselected
  · rintro ⟨hretained, hedge, heligible⟩
    refine ⟨key.retainedIndex, hretained, key.edgeIndex, hedge, ?_⟩
    simp [heligible]

private def x : FTerm := .var 0
private def a : FPred := .concept 0 x
private def b : FPred := .concept 1 x

private def retainedExample : List FCL :=
  [⟨[.P a], [.P b]⟩, ⟨[.P b], [.P a]⟩]

private def edgesExample : List PredEdge :=
  [{ receiverIndex := 3, label := .app 0 x, pushed := [a] },
   { receiverIndex := 4, label := .app 1 x, pushed := [b] }]

example : enumerate retainedExample edgesExample =
    [{ retainedIndex := 0, edgeIndex := 0 },
     { retainedIndex := 1, edgeIndex := 1 }] := by native_decide

example : eligible retainedExample edgesExample
    { retainedIndex := 0, edgeIndex := 1 } = false := by native_decide

#print axioms mem_enumerate_iff

end ContextCalculus.CBPredSendEnumeration
