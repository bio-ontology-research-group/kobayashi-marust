import ContextCalculus.CBSourceEqClosure
import ContextCalculus.CBPredSendEnumeration
import ContextCalculus.CBPredEnumeration

/-!
# Source-bound ordinary Pred closure

The live predecessor edges record production Pred-pool indexes already sent.
Lean recomputes that exact set from the final retained sender state. For every
sent payload it independently enumerates the receiver provider Cartesian
product and requires retained strengthening of every resulting arrival.

Nominal-ground r-Pred has a separate multi-edge eligibility rule and is not
claimed by this module.
-/

namespace ContextCalculus.CBSourceOrdinaryPredClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBInterContext
open ContextCalculus.CBInterContextWire
open ContextCalculus.CBLiveStateWire
open ContextCalculus.CBPredEnumeration
open ContextCalculus.CBPredSendEnumeration
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceEqClosure

def poolClause? (live : DecodedSourceLiveInsertionDerivationDocument)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) (poolIndex : Nat) : Option FCL := do
  let clauseId ← sender.predPoolIds[poolIndex]?
  if clauseId ∈ sender.retainedClauseIds then pure () else none
  let arena := if sender.rootDomain then live.rootArena else live.ordinaryArena
  arena[clauseId]?

def edgeView (edge : DecodedSourcePredecessorEdge production) : PredEdge :=
  { receiverIndex := edge.predecessorIndex.val
    label := edge.label
    pushed := edge.pushed }

def expectedPoolIndices
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena)
    (edge : DecodedSourcePredecessorEdge live.production) : List Nat :=
  (List.range sender.predPoolIds.length).filter fun poolIndex =>
    match poolClause? live sender poolIndex with
    | none => false
    | some clause =>
        predClauseEligible clause && edgeCoversBody (edgeView edge) clause

def providersOf
    (receiver : DecodedSourceLiveContext production ordinary rootArena)
    (dimensions : List (ProviderDimension receiver.retained))
    (selection : List (Fin receiver.retained.length)) :
    List (Fin receiver.retained.length × FLit) :=
  (dimensions.zip selection).map fun entry =>
    (entry.2, entry.1.1)

def arrivalConclusion
    (receiver : DecodedSourceLiveContext production ordinary rootArena) :
    FCL → List (Fin receiver.retained.length × FLit) → FCL
  | current, [] => current
  | current, provider :: rest =>
      arrivalConclusion receiver
        (resolvent (receiver.retained.get provider.1) current provider.2) rest

def arrivalCandidates
    (production : ContextCalculus.CBProductionTraceWire.DecodedProductionRun)
    (receiver : DecodedSourceLiveContext production ordinary rootArena)
    (payload : FCL) : List FCL :=
  match providerPlan receiver.retained payload.body with
  | none => []
  | some (dimensions, _) =>
      (cartesianSelections (dimensions.map Prod.snd)).map fun selection =>
        arrivalConclusion receiver payload (providersOf receiver dimensions selection)

def sentPayload?
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena)
    (edge : DecodedSourcePredecessorEdge live.production)
    (poolIndex : Nat) : Option FCL := do
  let clause ← poolClause? live sender poolIndex
  some (predTransfer (predBackwardSubstitution edge.label)
    (live.production.contexts.get sender.contextIndex).core clause)

def sentArrivalsClosedB
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena)
    (edge : DecodedSourcePredecessorEdge live.production) : Bool :=
  match live.contexts.find? fun receiver =>
      receiver.contextIndex = edge.predecessorIndex with
  | none => false
  | some receiver => edge.predPoolSeen.all fun poolIndex =>
      match sentPayload? live sender edge poolIndex with
      | none => false
      | some payload =>
          (arrivalCandidates live.production receiver payload).all fun candidate =>
            receiver.retained.any fun retained =>
              decide (Strengthens retained candidate)

def ordinaryPredClosedB
    (live : DecodedSourceLiveInsertionDerivationDocument) : Bool :=
  live.contexts.all fun sender =>
    if (live.production.contexts.get sender.contextIndex).nominalGround then true
    else sender.predecessors.all fun edge =>
      decide (edge.predPoolSeen = expectedPoolIndices live sender edge) &&
        sentArrivalsClosedB live sender edge

theorem ordinaryPredClosedB_exact_sends
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (hclosed : ordinaryPredClosedB live = true)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) (hsender : sender ∈ live.contexts)
    (hordinary :
      (live.production.contexts.get sender.contextIndex).nominalGround = false)
    (edge : DecodedSourcePredecessorEdge live.production)
    (hedge : edge ∈ sender.predecessors) :
    edge.predPoolSeen = expectedPoolIndices live sender edge := by
  have hsenderClosed := List.all_eq_true.mp hclosed sender hsender
  simp only [hordinary, Bool.false_eq_true, if_false, List.all_eq_true] at hsenderClosed
  have hedgeClosed := hsenderClosed edge hedge
  have hand : decide (edge.predPoolSeen = expectedPoolIndices live sender edge) = true ∧
      sentArrivalsClosedB live sender edge = true := by
    simpa only [Bool.and_eq_true] using hedgeClosed
  exact of_decide_eq_true hand.1

theorem ordinaryPredClosedB_arrivals
    (live : DecodedSourceLiveInsertionDerivationDocument)
    (hclosed : ordinaryPredClosedB live = true)
    (sender : DecodedSourceLiveContext live.production
      live.ordinaryArena live.rootArena) (hsender : sender ∈ live.contexts)
    (hordinary :
      (live.production.contexts.get sender.contextIndex).nominalGround = false)
    (edge : DecodedSourcePredecessorEdge live.production)
    (hedge : edge ∈ sender.predecessors) :
    sentArrivalsClosedB live sender edge = true := by
  have hsenderClosed := List.all_eq_true.mp hclosed sender hsender
  simp only [hordinary, Bool.false_eq_true, if_false, List.all_eq_true] at hsenderClosed
  have hand : decide (edge.predPoolSeen = expectedPoolIndices live sender edge) = true ∧
      sentArrivalsClosedB live sender edge = true := by
    simpa only [Bool.and_eq_true] using (hsenderClosed edge hedge)
  exact hand.2

structure WireSourceOrdinaryPredClosureDocument where
  version : Nat
  eq_closure : WireSourceEqClosureDocument
deriving Lean.FromJson, Lean.ToJson

structure DecodedSourceOrdinaryPredClosureDocument where
  eqClosure : DecodedSourceEqClosureDocument
  ordinary_pred_closed : ordinaryPredClosedB
    eqClosure.succClosure.join3Closure.hyperClosure.localClosure.live = true

def WireSourceOrdinaryPredClosureDocument.decode
    (wire : WireSourceOrdinaryPredClosureDocument) :
    Except String DecodedSourceOrdinaryPredClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported source-bound ordinary Pred-closure version {wire.version}"
  let eqClosure ← wire.eq_closure.decode
  let live := eqClosure.succClosure.join3Closure.hyperClosure.localClosure.live
  if hclosed : ordinaryPredClosedB live = true then
    return { eqClosure, ordinary_pred_closed := hclosed }
  else throw "source-bound CB terminal state is not ordinary-Pred-closed"

def WireSourceOrdinaryPredClosureDocument.check
    (wire : WireSourceOrdinaryPredClosureDocument) : Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireSourceOrdinaryPredClosureDocument.check_sound
    (wire : WireSourceOrdinaryPredClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceOrdinaryPredClosureDocument,
      wire.decode = .ok decoded ∧
      ordinaryPredClosedB
        decoded.eqClosure.succClosure.join3Closure.hyperClosure.localClosure.live = true := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireSourceOrdinaryPredClosureDocument.check, hdecode] at hcheck
  | ok decoded => exact ⟨decoded, rfl, decoded.ordinary_pred_closed⟩

#print axioms ordinaryPredClosedB_exact_sends
#print axioms ordinaryPredClosedB_arrivals
#print axioms WireSourceOrdinaryPredClosureDocument.check_sound

end ContextCalculus.CBSourceOrdinaryPredClosure
