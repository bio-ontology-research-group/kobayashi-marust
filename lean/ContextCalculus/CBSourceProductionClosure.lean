import ContextCalculus.CBSourceRootPredClosure

/-!
# Composed source-bound CB production closure

The individual source-bound checkers are nested deliberately, so one accepted
root-Pred document contains one typed source, one terminal snapshot, and every
local and inter-context closure witness.  This module exposes that fact as one
theorem instead of leaving the canonical-model bridge to combine unrelated
checker results.
-/

namespace ContextCalculus.CBSourceProductionClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBInterContextWire
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBSourceLocalClosure
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceJoin3Closure
open ContextCalculus.CBSourceSuccClosure
open ContextCalculus.CBSourceEqClosure
open ContextCalculus.CBSourceOrdinaryPredClosure
open ContextCalculus.CBSourceRootPredClosure

def ordinaryOf (decoded : DecodedSourceRootPredClosureDocument) :=
  decoded.ordinaryPredClosure

def eqOf (decoded : DecodedSourceRootPredClosureDocument) :=
  (ordinaryOf decoded).eqClosure

def succOf (decoded : DecodedSourceRootPredClosureDocument) :=
  (eqOf decoded).succClosure

def join3Of (decoded : DecodedSourceRootPredClosureDocument) :=
  (succOf decoded).join3Closure

def hyperOf (decoded : DecodedSourceRootPredClosureDocument) :=
  (join3Of decoded).hyperClosure

def localOf (decoded : DecodedSourceRootPredClosureDocument) :=
  (hyperOf decoded).localClosure

def liveOf (decoded : DecodedSourceRootPredClosureDocument) :=
  (localOf decoded).live

structure SourceProductionClosed
    (decoded : DecodedSourceRootPredClosureDocument) : Prop where
  terminalGlobal :
    (liveOf decoded).wirePendingMessages = 0 ∧
      (liveOf decoded).wireMessageTruncated = false ∧
      (liveOf decoded).wireNominalTruncated = false
  terminalContexts : ∀ context ∈ (liveOf decoded).contexts,
    context.wireTodoCount = 0 ∧ context.wireDirty = false ∧
      context.predHwm = context.predPoolIds.length ∧
      context.succHwm = context.succPoolIds.length ∧
      context.rSuccHwm = context.rSuccPoolIds.length ∧
      context.rSuccOffered = context.rSuccReach.length ∧
      context.wireRSuccEdgesGrew = false ∧
      ∀ edge ∈ context.successors,
        edge.reachHwm = context.rSuccReach.length
  retainedSound : ∀ (D : Type) (model : TModel D),
    (∀ source ∈ (liveOf decoded).production.source.ontology,
      valid model source) →
    ProductionRetainedValid (liveOf decoded).production model
  localResolution : ∀ context ∈ (liveOf decoded).production.contexts,
    ∀ candidate ∈ localResolutionCandidates context.retained,
      ∃ clause ∈ context.retained, Strengthens clause candidate
  localFactor : ∀ context ∈ (liveOf decoded).production.contexts,
    (∀ clause ∈ context.retained,
      CBLocalFactorClosureWire.terminalHeadNormal clause.head = true) ∧
    (∀ candidate ∈ CBLocalFactorClosureWire.factorCandidates context.retained,
      ∃ clause ∈ context.retained, Strengthens clause candidate.2)
  hyper : ∀ context ∈ (liveOf decoded).production.contexts,
    ∀ candidate ∈ CBSourceHyperClosure.hyperCandidates
        (hyperOf decoded).order context.root context.retained
        (liveOf decoded).production.source.ontology,
      ∃ clause ∈ context.retained, Strengthens clause candidate
  join3 : ∀ context ∈ (liveOf decoded).production.contexts,
    ∀ candidate ∈ CBSourceJoin3Closure.candidates
        (hyperOf decoded).order context.root context.retained,
      ∃ clause ∈ context.retained, Strengthens clause candidate.2
  directSucc : ∀ context ∈ (liveOf decoded).contexts,
    ∀ offer ∈ CBSourceSuccClosure.directOffers (hyperOf decoded).order
        (succOf decoded).rsuccEnabled (succOf decoded).reachConcepts
        context.rootDomain context.retained,
      CBSourceSuccClosure.offerDelivered (liveOf decoded)
        context.contextIndex.val offer = true
  rSucc : (succOf decoded).rsuccEnabled = true →
    ∀ context ∈ (liveOf decoded).contexts,
      ∀ offer ∈ CBSourceSuccClosure.sourceRSuccOffers
          (succOf decoded).reachConcepts (hyperOf decoded).order context,
        CBSourceSuccClosure.edgeDelivered (liveOf decoded)
            context.contextIndex.val offer.edge.targetIndex offer.edge.label
            offer.pushed = true ∧
          CBSourceSuccClosure.targetStrengthens (liveOf decoded)
            offer.edge.targetIndex offer.pushed = true
  eq : ∀ context ∈ (liveOf decoded).contexts,
    ∀ candidate ∈ CBSourceEqClosure.candidates (hyperOf decoded).order
        context.rootDomain context.retained,
      ∃ retained ∈ context.retained,
        Strengthens retained candidate.conclusion
  ordinaryPred : ordinaryPredClosedB (liveOf decoded) = true
  rootPred : rootPredClosedB (liveOf decoded) = true

theorem DecodedSourceRootPredClosureDocument.production_closed
    (decoded : DecodedSourceRootPredClosureDocument) :
    SourceProductionClosed decoded := by
  refine {
    terminalGlobal := (liveOf decoded).terminal_global
    terminalContexts := ?_
    retainedSound := ?_
    localResolution := (localOf decoded).local_resolution_closed
    localFactor := (localOf decoded).local_factor_closed
    hyper := (hyperOf decoded).complete_coverage
    join3 := (join3Of decoded).complete_coverage
    directSucc := ?_
    rSucc := ?_
    eq := ?_
    ordinaryPred := (ordinaryOf decoded).ordinary_pred_closed
    rootPred := decoded.root_pred_closed }
  · intro context hcontext
    exact (liveOf decoded).terminal_context context hcontext
  · intro D model hontology
    exact (liveOf decoded).production_retained_valid model hontology
  · intro context hcontext offer hoffer
    exact directSuccClosedB_sound (hyperOf decoded).order
      (succOf decoded).rsuccEnabled (succOf decoded).reachConcepts context
      ((succOf decoded).direct_closed context hcontext) offer hoffer
  · intro henabled context hcontext offer hoffer
    exact rSuccClosedB_sound (liveOf decoded) (succOf decoded).rsuccEnabled
      (succOf decoded).reachConcepts (hyperOf decoded).order context
      ((succOf decoded).rsucc_closed context hcontext) henabled offer hoffer
  · intro context hcontext candidate hcandidate
    exact sourceEqClosedB_sound (hyperOf decoded).order context
      ((eqOf decoded).eq_closed context hcontext) candidate hcandidate

theorem WireSourceRootPredClosureDocument.check_production_closed
    (wire : WireSourceRootPredClosureDocument)
    (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedSourceRootPredClosureDocument,
      wire.decode = .ok decoded ∧ SourceProductionClosed decoded := by
  cases hdecode : wire.decode with
  | error message =>
      simp [WireSourceRootPredClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      exact ⟨decoded, rfl,
        ContextCalculus.CBSourceProductionClosure.DecodedSourceRootPredClosureDocument.production_closed
          decoded⟩

#print axioms DecodedSourceRootPredClosureDocument.production_closed
#print axioms WireSourceRootPredClosureDocument.check_production_closed

end ContextCalculus.CBSourceProductionClosure
