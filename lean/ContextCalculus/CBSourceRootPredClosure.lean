import ContextCalculus.CBSourceOrdinaryPredClosure
import ContextCalculus.CBRootPredSendEnumeration

/-!
# Source-bound nominal-ground r-Pred closure

This layer binds KM's two nominal-ground sender branches to the terminal Rust
snapshot. Lean reconstructs every individual-labelled predecessor edge and
independently checks the x-free per-source multi-edge discharge branch and the
x-containing per-edge branch. Every exact send is then subjected to the same
complete receiver-provider Cartesian arrival check as ordinary Pred.
-/

namespace ContextCalculus.CBSourceRootPredClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBPredSendEnumeration
open ContextCalculus.CBRootPredSendEnumeration
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceOrdinaryPredClosure

def rootEdgeView?
    (edge : DecodedSourcePredecessorEdge production) : Option RootPredEdge :=
  match edge.label with
  | .const individual => some {
      receiverIndex := edge.predecessorIndex.val
      individual
      pushed := edge.pushed }
  | _ => none

def rootEdges?
    (sender : DecodedSourceLiveContext production ordinary rootArena) :
    Option (List RootPredEdge) :=
  sender.predecessors.mapM rootEdgeView?

def rootClauseEligible (nominalBase : Nat) (edges : List RootPredEdge)
    (edgeIndex : Nat) (clause : FCL) : Bool :=
  match edges[edgeIndex]? with
  | none => false
  | some edge =>
      if clauseMentionsX clause then
        predClauseEligible clause &&
          match bodyPredicates clause.body with
          | none => false
          | some body =>
              (body.all fun predicate => decide (predicate ∈ edge.pushed)) &&
              (clauseIndividuals clause).all fun individual =>
                edges.any fun announced =>
                  announced.receiverIndex = edge.receiverIndex &&
                    announced.individual = individual
      else
        representative edges edgeIndex && predClauseEligible clause &&
          match bodyPredicates clause.body with
          | none => false
          | some body =>
              body.all (dischargedBySource edges edge.receiverIndex) &&
              (clauseIndividuals clause).all
                (individualAnnounced edges edge.receiverIndex nominalBase)

def expectedRootPoolIndices
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena)
    (edges : List RootPredEdge) (edgeIndex : Nat) : List Nat :=
  (List.range sender.predPoolIds.length).filter fun poolIndex =>
    match poolClause? live sender poolIndex with
    | none => false
    | some clause => rootClauseEligible live.production.source.bounds.individuals
        edges edgeIndex clause

def rootPredClosedB
    (live : DecodedSourceLiveInsertionDerivationDocument) : Bool :=
  live.contexts.all fun sender =>
    if (live.production.contexts.get sender.contextIndex).nominalGround then
      match rootEdges? sender with
      | none => false
      | some edges =>
          (List.range sender.predecessors.length).all fun edgeIndex =>
            match sender.predecessors[edgeIndex]? with
            | none => false
            | some edge =>
                decide (edge.predPoolSeen =
                  expectedRootPoolIndices live sender edges edgeIndex) &&
                sentArrivalsClosedB live sender edge
    else true

theorem rootPredClosedB_exact_sends
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (hclosed : rootPredClosedB live = true)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) (hsender : sender ∈ live.contexts)
    (hroot :
      (live.production.contexts.get sender.contextIndex).nominalGround = true)
    (edges : List RootPredEdge) (hedges : rootEdges? sender = some edges)
    (edgeIndex : Nat) (hindex : edgeIndex < sender.predecessors.length) :
    (sender.predecessors.get ⟨edgeIndex, hindex⟩).predPoolSeen =
      expectedRootPoolIndices live sender edges edgeIndex := by
  have hsenderClosed := List.all_eq_true.mp hclosed sender hsender
  simp only [hroot, if_true, hedges, List.all_eq_true] at hsenderClosed
  have hindexClosed := hsenderClosed edgeIndex (List.mem_range.mpr hindex)
  rw [List.getElem?_eq_getElem hindex] at hindexClosed
  have hand :
      decide ((sender.predecessors.get ⟨edgeIndex, hindex⟩).predPoolSeen =
        expectedRootPoolIndices live sender edges edgeIndex) = true ∧
      sentArrivalsClosedB live sender
        (sender.predecessors.get ⟨edgeIndex, hindex⟩) = true := by
    simpa only [Bool.and_eq_true] using hindexClosed
  exact of_decide_eq_true hand.1

theorem rootPredClosedB_arrivals
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (hclosed : rootPredClosedB live = true)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) (hsender : sender ∈ live.contexts)
    (hroot :
      (live.production.contexts.get sender.contextIndex).nominalGround = true)
    (edges : List RootPredEdge) (hedges : rootEdges? sender = some edges)
    (edgeIndex : Nat) (hindex : edgeIndex < sender.predecessors.length) :
    sentArrivalsClosedB live sender
      (sender.predecessors.get ⟨edgeIndex, hindex⟩) = true := by
  have hsenderClosed := List.all_eq_true.mp hclosed sender hsender
  simp only [hroot, if_true, hedges, List.all_eq_true] at hsenderClosed
  have hindexClosed := hsenderClosed edgeIndex (List.mem_range.mpr hindex)
  rw [List.getElem?_eq_getElem hindex] at hindexClosed
  have hand :
      decide ((sender.predecessors.get ⟨edgeIndex, hindex⟩).predPoolSeen =
        expectedRootPoolIndices live sender edges edgeIndex) = true ∧
      sentArrivalsClosedB live sender
        (sender.predecessors.get ⟨edgeIndex, hindex⟩) = true := by
    simpa only [Bool.and_eq_true] using hindexClosed
  exact hand.2

structure WireSourceRootPredClosureDocument where
  version : Nat
  ordinary_pred_closure : WireSourceOrdinaryPredClosureDocument
deriving Lean.FromJson, Lean.ToJson

structure DecodedSourceRootPredClosureDocument where
  ordinaryPredClosure : DecodedSourceOrdinaryPredClosureDocument
  root_pred_closed : rootPredClosedB
    ordinaryPredClosure.eqClosure.succClosure.join3Closure.hyperClosure.localClosure.live = true

def WireSourceRootPredClosureDocument.decode
    (wire : WireSourceRootPredClosureDocument) :
    Except String DecodedSourceRootPredClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound root Pred-closure version {wire.version}"
  let ordinaryPredClosure ← wire.ordinary_pred_closure.decode
  let live := ordinaryPredClosure.eqClosure.succClosure.join3Closure.hyperClosure.localClosure.live
  if hclosed : rootPredClosedB live = true then
    return { ordinaryPredClosure, root_pred_closed := hclosed }
  else throw "source-bound CB terminal state is not root-Pred-closed"

def WireSourceRootPredClosureDocument.check
    (wire : WireSourceRootPredClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireSourceRootPredClosureDocument.check_sound
    (wire : WireSourceRootPredClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceRootPredClosureDocument,
      wire.decode = .ok decoded ∧
      rootPredClosedB decoded.ordinaryPredClosure.eqClosure.succClosure.join3Closure.hyperClosure.localClosure.live = true := by
  cases hdecode : wire.decode with
  | error message => simp [WireSourceRootPredClosureDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.root_pred_closed⟩

#print axioms rootPredClosedB_exact_sends
#print axioms rootPredClosedB_arrivals
#print axioms WireSourceRootPredClosureDocument.check_sound

end ContextCalculus.CBSourceRootPredClosure
