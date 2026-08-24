import ContextCalculus.CBRSuccClosureWire
import ContextCalculus.CBFiniteOrderAdmissibilityWire

/-!
# One globally closed production CB certificate

Most closure checkers are deliberately nested.  Equality closure and order
admissibility form a parallel branch because equality candidates need the
finished order.  This document joins that branch back to the Hyper/Join-3/
Succ/r-Succ branch and rejects any mismatch in source, terminal contexts, or
orders.  Successful decoding therefore denotes one run, not a collage of
certificates from different runs.
-/

namespace ContextCalculus.CBGlobalClosureWire

open Lean ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBTermWire
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBRSuccClosureWire
open ContextCalculus.CBSuccClosureWire
open ContextCalculus.CBRSuccClosure
open ContextCalculus.CBInterContext
open ContextCalculus.CBFiniteOrderAdmissibilityWire

def rProduction (rsucc : DecodedRSuccClosureDocument) :=
  CBRSuccClosureWire.productionOf rsucc.succ

def eProduction (order : DecodedFiniteOrderAdmissibilityDocument) :=
  let terminal :=
    order.eqClosure.literalOrder.termOrder.factorClosure.localResolution.terminal
  terminal.sendCoverage.interContext.base.production

def contextSnapshot {bounds : CBTermWire.Bounds} {ontology : List FCL}
    (contexts : List (DecodedProductionContext bounds ontology)) :
    List (Nat × List FCL) :=
  contexts.map fun context => (context.contextId, context.retained)

structure WireCBGlobalClosureDocument where
  version : Nat
  rsucc_closure : WireRSuccClosureDocument
  order_admissibility : WireFiniteOrderAdmissibilityDocument
deriving FromJson, ToJson

structure DecodedCBGlobalClosureDocument where
  rsucc : DecodedRSuccClosureDocument
  order : DecodedFiniteOrderAdmissibilityDocument
  source_bounds_eq : (rProduction rsucc).source.bounds =
    (eProduction order).source.bounds
  source_ontology_eq : (rProduction rsucc).source.ontology =
    (eProduction order).source.ontology
  runtime_bounds_eq : (rProduction rsucc).bounds = (eProduction order).bounds
  contexts_eq : contextSnapshot (rProduction rsucc).contexts =
    contextSnapshot (eProduction order).contexts
  terms_eq : rsucc.succ.join3.hyper.literalOrder.termOrder.orderedTerms =
    order.eqClosure.literalOrder.termOrder.orderedTerms
  literals_eq : rsucc.succ.join3.hyper.literalOrder.orderedLiterals =
    order.eqClosure.literalOrder.orderedLiterals

def WireCBGlobalClosureDocument.decode (wire : WireCBGlobalClosureDocument) :
    Except String DecodedCBGlobalClosureDocument := do
  if wire.version != 1 then
    throw s!"unsupported CB global-closure version {wire.version}"
  let rsucc ← wire.rsucc_closure.decode
  let order ← wire.order_admissibility.decode
  if hsourceBounds : (rProduction rsucc).source.bounds =
      (eProduction order).source.bounds then
    if hsource : (rProduction rsucc).source.ontology =
        (eProduction order).source.ontology then
      if hruntime : (rProduction rsucc).bounds = (eProduction order).bounds then
        if hcontexts : contextSnapshot (rProduction rsucc).contexts =
            contextSnapshot (eProduction order).contexts then
          if hterms : rsucc.succ.join3.hyper.literalOrder.termOrder.orderedTerms =
              order.eqClosure.literalOrder.termOrder.orderedTerms then
            if hliterals : rsucc.succ.join3.hyper.literalOrder.orderedLiterals =
                order.eqClosure.literalOrder.orderedLiterals then
              return {
                rsucc := rsucc
                order := order
                source_bounds_eq := hsourceBounds
                source_ontology_eq := hsource
                runtime_bounds_eq := hruntime
                contexts_eq := hcontexts
                terms_eq := hterms
                literals_eq := hliterals
              }
            else throw "CB equality and inter-context branches use different literal orders"
          else throw "CB equality and inter-context branches use different term orders"
        else throw "CB equality and inter-context branches use different terminal contexts"
      else throw "CB equality and inter-context branches use different runtime bounds"
    else throw "CB equality and inter-context branches use different source ontologies"
  else throw "CB equality and inter-context branches use different source bounds"

def WireCBGlobalClosureDocument.check (wire : WireCBGlobalClosureDocument) :
    Except String Bool := do
  let _ ← wire.decode
  return true

theorem WireCBGlobalClosureDocument.check_sound
    (wire : WireCBGlobalClosureDocument) (hcheck : wire.check = .ok true) :
    ∃ decoded : DecodedCBGlobalClosureDocument,
      wire.decode = .ok decoded ∧
      contextSnapshot (rProduction decoded.rsucc).contexts =
        contextSnapshot (eProduction decoded.order).contexts ∧
      decoded.rsucc.succ.join3.hyper.literalOrder.termOrder.orderedTerms =
        decoded.order.eqClosure.literalOrder.termOrder.orderedTerms ∧
      decoded.rsucc.succ.join3.hyper.literalOrder.orderedLiterals =
        decoded.order.eqClosure.literalOrder.orderedLiterals ∧
      subtermCondition decoded.order.eqClosure.literalOrder.termOrder = true ∧
      unaryMonotoneCondition decoded.order.eqClosure.literalOrder.termOrder = true ∧
      ∀ context ∈ decoded.rsucc.contexts,
        ∀ offer ∈ rSuccOffers (sendCoverageOf decoded.rsucc.succ)
            decoded.rsucc.reachConcepts
            decoded.rsucc.succ.join3.hyper.literalOrder
            context.sourceIndex.val
            ((productionOf decoded.rsucc.succ).contexts.get
              context.sourceIndex).retained,
          ∃ targetIndex strengtheningIndex,
            offer.edge.targetIndex = targetIndex.val ∧
            edgeDelivered decoded.rsucc.succ.join3 context.sourceIndex.val
              targetIndex.val { edge := offer.edge.label, pushed := offer.pushed } = true ∧
            Strengthens
              (((productionOf decoded.rsucc.succ).contexts.get targetIndex).retained.get
                strengtheningIndex) (succHypothesis offer.pushed) := by
  cases hdecode : wire.decode with
  | error message => simp [WireCBGlobalClosureDocument.check, hdecode] at hcheck
  | ok decoded =>
      refine ⟨decoded, rfl, decoded.contexts_eq, decoded.terms_eq,
        decoded.literals_eq, decoded.order.subterm_condition,
        decoded.order.unary_monotone_condition, ?_⟩
      intro context _
      exact context.complete_delivery

#print axioms WireCBGlobalClosureDocument.check_sound

end ContextCalculus.CBGlobalClosureWire
