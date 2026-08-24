import ContextCalculus.CBGroundResolutionBridge
import ContextCalculus.CBLocalPropositionalModel
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
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBProductionTrace
open ContextCalculus.CBLocalPropositionalModel
open ContextCalculus.CBLocalFactorClosureWire
open ContextCalculus.CBSourceEqClosure

theorem SourceProductionClosed.retained_head_normal
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained) :
    terminalHeadNormal clause.head = true :=
  (closed.localFactor context hcontext).1 clause hclause

theorem SourceProductionClosed.retained_head_equality_normal
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained) :
    (∀ term, FLit.eq term term ∉ clause.head) ∧
    (∀ term, FLit.ineq term term ∉ clause.head) ∧
    (∀ left right, FLit.eq left right ∈ clause.head →
      FLit.ineq left right ∉ clause.head) := by
  have hnormal :=
    ContextCalculus.CBSourceGroundResolutionBridge.SourceProductionClosed.retained_head_normal
      closed context hcontext clause hclause
  exact ⟨terminalHeadNormal_no_reflexive_eq hnormal,
    terminalHeadNormal_no_reflexive_ineq hnormal,
    fun _ _ => terminalHeadNormal_no_complement hnormal⟩

theorem SourceProductionClosed.retained_factor_pair_covered
    {decoded : DecodedSourceRootPredClosureDocument}
    (_closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (sourceIndex firstHeadIndex secondHeadIndex : Nat)
    (source : FCL) (hsource : context.retained[sourceIndex]? = some source)
    (common first second : FTerm)
    (hfirst : source.head[firstHeadIndex]? = some (.eq common first))
    (hsecond : source.head[secondHeadIndex]? = some (.eq common second))
    (hdistinct : second ≠ first)
    (filtered : List FLit)
    (hnormalize : normalizeGeneratedHead
      (factorConclusion source common first second).head = some filtered) :
    ∃ retained ∈ context.retained,
      CBProductionTrace.Strengthens retained
        { factorConclusion source common first second with head := filtered } :=
  (localOf decoded).factor_pair_covered context hcontext sourceIndex
    firstHeadIndex secondHeadIndex source hsource common first second hfirst
    hsecond hdistinct filtered hnormalize

theorem SourceProductionClosed.retained_eq_pair_covered
    {decoded : DecodedSourceRootPredClosureDocument}
    (_closed : SourceProductionClosed decoded)
    (context : DecodedSourceLiveContext (liveOf decoded).production
      (liveOf decoded).ordinaryArena (liveOf decoded).rootArena)
    (hcontext : context ∈ (liveOf decoded).contexts)
    (equalityIndex equalityHeadIndex targetIndex targetHeadIndex : Nat)
    (equalityClause targetClause : FCL)
    (hequalityClause : context.retained[equalityIndex]? = some equalityClause)
    (htargetClause : context.retained[targetIndex]? = some targetClause)
    (hmaxEquality : equalityHeadIndex ∈
      (hyperOf decoded).order.maximalHeadIndices context.rootDomain
        equalityClause.head)
    (hmaxTarget : targetHeadIndex ∈
      (hyperOf decoded).order.maximalHeadIndices context.rootDomain
        targetClause.head)
    (left right : FTerm)
    (hequality : equalityClause.head[equalityHeadIndex]? =
      some (.eq left right))
    (target rewritten : FLit)
    (htarget : targetClause.head[targetHeadIndex]? = some target)
    (hdifferent : target ≠ .eq left right)
    (hrewrite : directRewrite (hyperOf decoded).order left right target =
      some rewritten)
    (hproduction : CBLocalEqEnumeration.productionCase left right target = true)
    (filtered : List FLit)
    (hnormalize : normalizeGeneratedHead
      (CBLocalEqEnumeration.directParamodulant targetClause equalityClause
        target (.eq left right) rewritten).head = some filtered) :
    ∃ retained ∈ context.retained,
      CBProductionTrace.Strengthens retained
        { CBLocalEqEnumeration.directParamodulant targetClause equalityClause
            target (.eq left right) rewritten with head := filtered } :=
  sourceEq_pair_covered (hyperOf decoded).order context
    ((eqOf decoded).eq_closed context hcontext)
    equalityIndex equalityHeadIndex targetIndex targetHeadIndex equalityClause
    targetClause hequalityClause htargetClause hmaxEquality hmaxTarget left right
    hequality target rewritten htarget hdifferent hrewrite hproduction filtered
    hnormalize

/-- Feature-independent local candidate valuation obtained from the same
source-bound production certificate. Equality coherence is established by the
subsequent Factor/Eq bridge. -/
theorem SourceProductionClosed.context_raw_model
    [LinearOrder FLit] [WellFoundedLT FLit]
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (hbot : PClause.bot ∉ rawSet context.retained) :
    ∃ valuation : FLit → Prop,
      ∀ clause ∈ context.retained,
        ContextCalculus.sat valuation clause :=
  local_raw_model context.retained
    (closed.localResolution context hcontext) hbot

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
#print axioms SourceProductionClosed.context_raw_model
#print axioms SourceProductionClosed.retained_head_equality_normal
#print axioms SourceProductionClosed.retained_factor_pair_covered
#print axioms SourceProductionClosed.retained_eq_pair_covered

end ContextCalculus.CBSourceGroundResolutionBridge
