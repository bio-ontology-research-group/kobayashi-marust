import ContextCalculus.CBGlobalClosureWire

/-!
# Semantic surface of the global production-closure certificate

`CBGlobalClosureWire` checks one nested document, but its original public
theorem exposed only the final r-Succ and order facts.  This file projects the
same decoded document into closure statements for every local and
inter-context production rule family.  The quantification is over every
production context, not merely over the contexts supplied by the certificate.
-/

namespace ContextCalculus.CBGlobalProductionClosure

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBGlobalClosureWire
open ContextCalculus.CBLocalResolutionClosureWire
open ContextCalculus.CBLocalFactorClosureWire
open ContextCalculus.CBLocalEqClosureWire
open ContextCalculus.CBHyperClosureWire
open ContextCalculus.CBJoin3ClosureWire
open ContextCalculus.CBSuccClosureWire
open ContextCalculus.CBRSuccClosureWire
open ContextCalculus.CBLocalEqEnumeration
open ContextCalculus.CBHyperClosure
open ContextCalculus.CBJoin3Closure
open ContextCalculus.CBSuccClosure
open ContextCalculus.CBRSuccClosure
open ContextCalculus.CBInterContext

private theorem exists_indexed_context
    (contexts : List Context) (indexOf : Context → Nat)
    (exact : contexts.map indexOf = List.range count)
    (index : Fin count) :
    ∃ context ∈ contexts, indexOf context = index.val := by
  have hmem : index.val ∈ List.range count := List.mem_range.mpr index.isLt
  rw [← exact] at hmem
  simpa only [List.mem_map] using hmem

def localResolutionOf (decoded : DecodedCBGlobalClosureDocument) :=
  decoded.order.eqClosure.literalOrder.termOrder.factorClosure.localResolution

def factorOf (decoded : DecodedCBGlobalClosureDocument) :=
  decoded.order.eqClosure.literalOrder.termOrder.factorClosure

def eqOf (decoded : DecodedCBGlobalClosureDocument) := decoded.order.eqClosure

def hyperOf (decoded : DecodedCBGlobalClosureDocument) :=
  decoded.rsucc.succ.join3.hyper

def join3Of (decoded : DecodedCBGlobalClosureDocument) :=
  decoded.rsucc.succ.join3

def succOf (decoded : DecodedCBGlobalClosureDocument) := decoded.rsucc.succ

def productionOfGlobal (decoded : DecodedCBGlobalClosureDocument) :=
  CBGlobalClosureWire.rProduction decoded.rsucc

def localProductionOf (decoded : DecodedCBGlobalClosureDocument) :=
  (localResolutionOf decoded).terminal.sendCoverage.interContext.base.production

def eqProductionOf (decoded : DecodedCBGlobalClosureDocument) :=
  CBLocalEqClosureWire.productionContexts (eqOf decoded).literalOrder

def LocalResolutionClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (localProductionOf decoded).contexts.length) : Prop :=
  let resolution := localResolutionOf decoded
  ∃ context ∈ resolution.contexts,
    context.contextIndex.val = index.val ∧
    context.generated.map (·.signature) =
      CBLocalResolutionClosureWire.resolutionSignatures
        ((localProductionOf decoded).contexts.get context.contextIndex).retained ∧
    ∀ coverage ∈ context.generated,
      Strengthens
        (((localProductionOf decoded).contexts.get context.contextIndex).retained.get
          coverage.strengtheningIndex)
        (resolvent
          (((localProductionOf decoded).contexts.get context.contextIndex).retained.get
            coverage.positiveIndex)
          (((localProductionOf decoded).contexts.get context.contextIndex).retained.get
            coverage.negativeIndex)
          coverage.literal)

def FactorClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (localProductionOf decoded).contexts.length) : Prop :=
  let factor := factorOf decoded
  ∃ context ∈ factor.contexts,
    context.contextIndex.val = index.val ∧
    (∀ clause ∈ ((localProductionOf decoded).contexts.get context.contextIndex).retained,
      CBLocalFactorClosureWire.terminalHeadNormal clause.head = true) ∧
    context.generated.map (fun coverage =>
      (coverage.signature, coverage.conclusion)) =
      CBLocalFactorClosureWire.factorCandidates
        ((localProductionOf decoded).contexts.get context.contextIndex).retained ∧
    ∀ coverage ∈ context.generated,
      Strengthens
        (((localProductionOf decoded).contexts.get context.contextIndex).retained.get
          coverage.strengtheningIndex)
        coverage.conclusion

def EqClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (eqProductionOf decoded).length) : Prop :=
  let eqClosure := eqOf decoded
  ∃ context ∈ eqClosure.contexts,
    context.contextIndex.val = index.val ∧
    context.generated.map (fun coverage => coverage.candidate) =
      eqCandidates eqClosure.literalOrder
        ((eqProductionOf decoded).get context.contextIndex).retained ∧
    ∀ coverage ∈ context.generated,
      Strengthens
        (((eqProductionOf decoded).get context.contextIndex).retained.get
          coverage.strengtheningIndex)
        coverage.conclusion

def HyperClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (productionOfGlobal decoded).contexts.length) : Prop :=
  let hyper := hyperOf decoded
  ∀ candidate ∈ hyperCandidates hyper.literalOrder
      hyper.literalOrder.termOrder.orderedTerms
      ((productionOfGlobal decoded).contexts.get index).retained
      (productionOfGlobal decoded).source.ontology,
    ∃ strengtheningIndex,
      Strengthens
        (((productionOfGlobal decoded).contexts.get index).retained.get
          strengtheningIndex)
        candidate

def Join3ClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (productionOfGlobal decoded).contexts.length) : Prop :=
  let join3 := join3Of decoded
  ∀ candidate ∈ candidates join3.hyper.literalOrder
      ((productionOfGlobal decoded).contexts.get index).retained,
    ∃ strengtheningIndex,
      Strengthens
        (((productionOfGlobal decoded).contexts.get index).retained.get
          strengtheningIndex)
        candidate.2

def SuccClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (productionOfGlobal decoded).contexts.length) : Prop :=
  let succ := succOf decoded
  ∀ offer ∈ directOffers succ.join3.hyper.literalOrder
      ((productionOfGlobal decoded).contexts.get index).retained,
    ∃ targetIndex strengtheningIndex,
      edgeDelivered succ.join3 index.val targetIndex.val offer = true ∧
      Strengthens
        (((productionOfGlobal decoded).contexts.get targetIndex).retained.get
          strengtheningIndex)
        (succHypothesis offer.pushed)

def RSuccClosedAt (decoded : DecodedCBGlobalClosureDocument)
    (index : Fin (productionOfGlobal decoded).contexts.length) : Prop :=
  ∀ offer ∈ rSuccOffers
      (CBRSuccClosureWire.sendCoverageOf decoded.rsucc.succ)
      decoded.rsucc.reachConcepts decoded.rsucc.succ.join3.hyper.literalOrder
      index.val ((productionOfGlobal decoded).contexts.get index).retained,
    ∃ targetIndex strengtheningIndex,
      offer.edge.targetIndex = targetIndex.val ∧
      edgeDelivered decoded.rsucc.succ.join3 index.val
        targetIndex.val { edge := offer.edge.label, pushed := offer.pushed } = true ∧
      Strengthens
        (((productionOfGlobal decoded).contexts.get targetIndex).retained.get
          strengtheningIndex)
        (succHypothesis offer.pushed)

structure GlobalProductionClosed
    (decoded : DecodedCBGlobalClosureDocument) : Prop where
  localResolution : ∀ index, LocalResolutionClosedAt decoded index
  factor : ∀ index, FactorClosedAt decoded index
  eq : ∀ index, EqClosedAt decoded index
  hyper : ∀ index, HyperClosedAt decoded index
  join3 : ∀ index, Join3ClosedAt decoded index
  succ : ∀ index, SuccClosedAt decoded index
  rsucc : ∀ index, RSuccClosedAt decoded index

theorem DecodedCBGlobalClosureDocument.production_closed
    (decoded : DecodedCBGlobalClosureDocument) :
    GlobalProductionClosed decoded := by
  refine {
    localResolution := ?_
    factor := ?_
    eq := ?_
    hyper := ?_
    join3 := ?_
    succ := ?_
    rsucc := ?_ }
  · intro index
    let resolution := localResolutionOf decoded
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      resolution.contexts (fun context => context.contextIndex.val)
      resolution.context_indices_exact index
    refine ⟨context, hcontext, hindex, context.signatures_exact, ?_⟩
    intro coverage _
    exact coverage.strengthens
  · intro index
    let factor := factorOf decoded
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      factor.contexts (fun context => context.contextIndex.val)
      factor.context_indices_exact index
    refine ⟨context, hcontext, hindex, context.heads_normal,
      context.candidates_exact, ?_⟩
    intro coverage _
    exact coverage.strengthens
  · intro index
    let eqClosure := eqOf decoded
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      eqClosure.contexts (fun context => context.contextIndex.val)
      eqClosure.context_indices_exact index
    refine ⟨context, hcontext, hindex, context.candidates_exact, ?_⟩
    intro coverage _
    exact coverage.strengthens
  · intro index
    let hyper := hyperOf decoded
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      hyper.contexts (fun context => context.contextIndex.val)
      hyper.context_indices_exact index
    have hindex' : context.contextIndex = index := Fin.ext hindex
    subst index
    exact context.complete_coverage
  · intro index
    let join3 := join3Of decoded
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      join3.contexts (fun context => context.contextIndex.val)
      join3.context_indices_exact index
    have hindex' : context.contextIndex = index := Fin.ext hindex
    subst index
    exact context.complete_coverage
  · intro index
    let succ := succOf decoded
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      succ.contexts (fun context => context.senderIndex.val)
      succ.context_indices_exact index
    have hindex' : context.senderIndex = index := Fin.ext hindex
    subst index
    exact context.complete_delivery
  · intro index
    obtain ⟨context, hcontext, hindex⟩ := exists_indexed_context
      decoded.rsucc.contexts (fun context => context.sourceIndex.val)
      decoded.rsucc.context_indices_exact index
    have hindex' : context.sourceIndex = index := Fin.ext hindex
    subst index
    exact context.complete_delivery

#print axioms DecodedCBGlobalClosureDocument.production_closed

end ContextCalculus.CBGlobalProductionClosure
