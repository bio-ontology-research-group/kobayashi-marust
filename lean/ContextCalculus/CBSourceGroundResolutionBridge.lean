import ContextCalculus.CBGroundResolutionBridge
import ContextCalculus.CBSourceProductionClosure

/-!
# Source-bound local ground models

This module consumes the composed production certificate, rather than a free
local-closure hypothesis, and builds the ordered canonical valuation for every
clash-free inequality-free terminal context.
-/

namespace ContextCalculus.CBSourceGroundResolutionBridge

open ContextCalculus ContextCalculus.CheckerTerm ContextCalculus.PropRes
open ContextCalculus.CBGroundEqualityBridge
open ContextCalculus.CBGroundResolutionBridge
open ContextCalculus.CBSourceProductionClosure
open ContextCalculus.CBSourceRootPredClosure
open ContextCalculus.CBProductionTraceWire

theorem SourceProductionClosed.context_ground_model
    [LinearOrder GroundAtom] [WellFoundedLT GroundAtom]
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (hfree : ∀ clause ∈ context.retained, InequalityFree clause)
    (hbot : PClause.bot ∉ groundSet context.retained) :
    ∃ valuation : GroundAtom → Prop,
      ∀ clause ∈ context.retained,
        sat (evalGroundLiteral valuation) clause :=
  local_ground_model context.retained hfree
    (closed.localResolution context hcontext) hbot

theorem SourceProductionClosed.all_context_ground_models
    [LinearOrder GroundAtom] [WellFoundedLT GroundAtom]
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (hfree : ∀ context ∈ (liveOf decoded).production.contexts,
      ∀ clause ∈ context.retained, InequalityFree clause)
    (hbot : ∀ context ∈ (liveOf decoded).production.contexts,
      PClause.bot ∉ groundSet context.retained) :
    ∀ context ∈ (liveOf decoded).production.contexts,
      ∃ valuation : GroundAtom → Prop,
        ∀ clause ∈ context.retained,
          sat (evalGroundLiteral valuation) clause := by
  intro context hcontext
  exact SourceProductionClosed.context_ground_model closed context hcontext
    (hfree context hcontext) (hbot context hcontext)

#print axioms SourceProductionClosed.context_ground_model
#print axioms SourceProductionClosed.all_context_ground_models

end ContextCalculus.CBSourceGroundResolutionBridge
