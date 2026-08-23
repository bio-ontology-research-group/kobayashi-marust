import ContextCalculus.CBPredSendEnumeration

/-!
# Exact x-free nominal r-Pred send enumeration

The nominal ground context uses a different sender condition from ordinary
Pred.  One body atom may be discharged by an individual-labelled edge that is
different from the edge discharging another body atom, provided all those
edges have the same receiving source context.  KM then sends one message per
source, using its smallest edge label as a stable representative.

This module specifies that finite scan independently and proves exact
membership. It also specifies the ground-context clauses that mention `x`:
those retain KM's per-edge path, requiring one edge to cover the entire body
and requiring that source to have announced every individual in the clause.
Terminal wire binding is a separate layer.
-/

namespace ContextCalculus.CBRootPredSendEnumeration

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBPredSendEnumeration

structure RootPredEdge where
  receiverIndex : Nat
  individual : Nat
  pushed : List FPred
deriving DecidableEq, Repr

structure RootSendKey where
  retainedIndex : Nat
  edgeIndex : Nat
deriving DecidableEq, Repr

def termMentionsX : FTerm → Bool
  | .var index => index = 0
  | .const _ => false
  | .app _ argument => termMentionsX argument

def predMentionsX : FPred → Bool
  | .concept _ term => termMentionsX term
  | .role _ source target => termMentionsX source || termMentionsX target

def litMentionsX : FLit → Bool
  | .P predicate => predMentionsX predicate
  | .eq left right | .ineq left right =>
      termMentionsX left || termMentionsX right

def clauseMentionsX (clause : FCL) : Bool :=
  clause.body.any litMentionsX || clause.head.any litMentionsX

def termIndividuals : FTerm → List Nat
  | .var _ => []
  | .const individual => [individual]
  | .app _ argument => termIndividuals argument

def predIndividuals : FPred → List Nat
  | .concept _ term => termIndividuals term
  | .role _ source target => termIndividuals source ++ termIndividuals target

def litIndividuals : FLit → List Nat
  | .P predicate => predIndividuals predicate
  | .eq left right | .ineq left right =>
      termIndividuals left ++ termIndividuals right

def clauseIndividuals (clause : FCL) : List Nat :=
  (clause.body.flatMap litIndividuals) ++
    clause.head.flatMap litIndividuals

def earlierRepresentative (edges : List RootPredEdge) (edgeIndex : Nat) : Bool :=
  match edges[edgeIndex]? with
  | none => false
  | some edge =>
      (List.range edgeIndex).any fun earlierIndex =>
        match edges[earlierIndex]? with
        | some earlier =>
            earlier.receiverIndex = edge.receiverIndex &&
              earlier.individual ≤ edge.individual
        | none => false

def representative (edges : List RootPredEdge) (edgeIndex : Nat) : Bool :=
  match edges[edgeIndex]? with
  | none => false
  | some edge =>
      !earlierRepresentative edges edgeIndex &&
        !(List.range edges.length).any fun otherIndex =>
          match edges[otherIndex]? with
          | some other =>
              other.receiverIndex = edge.receiverIndex &&
                other.individual < edge.individual
          | none => false

def dischargedBySource (edges : List RootPredEdge) (receiverIndex : Nat)
    (predicate : FPred) : Bool :=
  (predIndividuals predicate).any fun individual =>
    edges.any fun edge =>
      edge.receiverIndex = receiverIndex &&
      edge.individual = individual &&
      decide (predicate ∈ edge.pushed)

def individualAnnounced (edges : List RootPredEdge) (receiverIndex : Nat)
    (nominalBase individual : Nat) : Bool :=
  nominalBase ≤ individual || edges.any fun edge =>
    edge.receiverIndex = receiverIndex && edge.individual = individual

def eligible (nominalBase : Nat) (retained : List FCL)
    (edges : List RootPredEdge) (key : RootSendKey) : Bool :=
  match retained[key.retainedIndex]?, edges[key.edgeIndex]? with
  | some clause, some edge =>
      predClauseEligible clause &&
      !clauseMentionsX clause &&
      match bodyPredicates clause.body with
      | none => false
      | some body =>
          body.all (dischargedBySource edges edge.receiverIndex) &&
          (clauseIndividuals clause).all
            (individualAnnounced edges edge.receiverIndex nominalBase)
  | _, _ => false

def enumerate (nominalBase : Nat) (retained : List FCL)
    (edges : List RootPredEdge) : List RootSendKey :=
  (List.range retained.length).flatMap fun retainedIndex =>
    (List.range edges.length).filterMap fun edgeIndex =>
      let key := { retainedIndex, edgeIndex }
      if representative edges edgeIndex &&
          eligible nominalBase retained edges key then
        some key
      else none

theorem mem_enumerate_iff (nominalBase : Nat) (retained : List FCL)
    (edges : List RootPredEdge) (key : RootSendKey) :
    key ∈ enumerate nominalBase retained edges ↔
      key.retainedIndex < retained.length ∧
      key.edgeIndex < edges.length ∧
      representative edges key.edgeIndex = true ∧
      eligible nominalBase retained edges key = true := by
  simp only [enumerate, List.mem_flatMap, List.mem_range,
    List.mem_filterMap]
  constructor
  · rintro ⟨retainedIndex, hretained, edgeIndex, hedge, hselected⟩
    split at hselected
    next haccepted =>
      simp only [Option.some.injEq] at hselected
      subst key
      simp only [Bool.and_eq_true] at haccepted
      exact ⟨hretained, hedge, haccepted.1, haccepted.2⟩
    next => simp at hselected
  · rintro ⟨hretained, hedge, hrepresentative, heligible⟩
    refine ⟨key.retainedIndex, hretained, key.edgeIndex, hedge, ?_⟩
    simp [hrepresentative, heligible]

/-! ## Ground-context clauses that retain the per-edge path -/

def xEligible (retained : List FCL) (edges : List RootPredEdge)
    (key : RootSendKey) : Bool :=
  match retained[key.retainedIndex]?, edges[key.edgeIndex]? with
  | some clause, some edge =>
      predClauseEligible clause &&
      clauseMentionsX clause &&
      match bodyPredicates clause.body with
      | none => false
      | some body =>
          (body.all fun predicate => decide (predicate ∈ edge.pushed)) &&
          (clauseIndividuals clause).all fun individual =>
            edges.any fun announced =>
              announced.receiverIndex = edge.receiverIndex &&
                announced.individual = individual
  | _, _ => false

def enumerateX (retained : List FCL) (edges : List RootPredEdge) :
    List RootSendKey :=
  (List.range retained.length).flatMap fun retainedIndex =>
    (List.range edges.length).filterMap fun edgeIndex =>
      let key := { retainedIndex, edgeIndex }
      if xEligible retained edges key then some key else none

theorem mem_enumerateX_iff (retained : List FCL)
    (edges : List RootPredEdge) (key : RootSendKey) :
    key ∈ enumerateX retained edges ↔
      key.retainedIndex < retained.length ∧
      key.edgeIndex < edges.length ∧
      xEligible retained edges key = true := by
  simp only [enumerateX, List.mem_flatMap, List.mem_range,
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

/-! ## Exact production branch composition -/

def combinedEligible (nominalBase : Nat) (retained : List FCL)
    (edges : List RootPredEdge) (key : RootSendKey) : Bool :=
  match retained[key.retainedIndex]? with
  | none => false
  | some clause =>
      if clauseMentionsX clause then
        xEligible retained edges key
      else
        representative edges key.edgeIndex &&
          eligible nominalBase retained edges key

/-- Clause-major branch composition matching KM: each clause takes exactly
one of the x-containing per-edge path and the x-free per-source path. -/
def enumerateAll (nominalBase : Nat) (retained : List FCL)
    (edges : List RootPredEdge) : List RootSendKey :=
  (List.range retained.length).flatMap fun retainedIndex =>
    (List.range edges.length).filterMap fun edgeIndex =>
      let key := { retainedIndex, edgeIndex }
      if combinedEligible nominalBase retained edges key then some key else none

theorem mem_enumerateAll_iff (nominalBase : Nat) (retained : List FCL)
    (edges : List RootPredEdge) (key : RootSendKey) :
    key ∈ enumerateAll nominalBase retained edges ↔
      key.retainedIndex < retained.length ∧
      key.edgeIndex < edges.length ∧
      combinedEligible nominalBase retained edges key = true := by
  simp only [enumerateAll, List.mem_flatMap, List.mem_range,
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

private def o (id : Nat) : FTerm := .const id
private def p (id individual : Nat) : FPred :=
  .concept id (o individual)

private def retainedExample : List FCL :=
  [⟨[.P (p 0 0), .P (p 1 1)], [.P (p 2 2)]⟩]

private def edgesExample : List RootPredEdge :=
  [{ receiverIndex := 4, individual := 1, pushed := [p 1 1] },
   { receiverIndex := 4, individual := 0, pushed := [p 0 0] },
   { receiverIndex := 5, individual := 0, pushed := [p 0 0] }]

example : enumerate 2 retainedExample edgesExample =
    [{ retainedIndex := 0, edgeIndex := 1 }] := by native_decide

example : eligible 3 retainedExample edgesExample
    { retainedIndex := 0, edgeIndex := 1 } = false := by native_decide

private def retainedXExample : List FCL :=
  [⟨[.P (.concept 0 (.var 0))],
      [.P (.role 0 (.var 0) (o 1))]⟩]

private def edgesXExample : List RootPredEdge :=
  [{ receiverIndex := 4, individual := 0,
      pushed := [.concept 0 (.var 0)] },
   { receiverIndex := 4, individual := 1, pushed := [] }]

example : enumerateX retainedXExample edgesXExample =
    [{ retainedIndex := 0, edgeIndex := 0 }] := by native_decide

example : enumerateX retainedXExample (edgesXExample.take 1) = [] := by
  native_decide

example : enumerateAll 2 (retainedExample ++ retainedXExample)
    (edgesExample ++ edgesXExample) =
    [{ retainedIndex := 0, edgeIndex := 1 },
     { retainedIndex := 1, edgeIndex := 3 }] := by native_decide

#print axioms mem_enumerate_iff
#print axioms mem_enumerateX_iff
#print axioms mem_enumerateAll_iff

end ContextCalculus.CBRootPredSendEnumeration
