import ContextCalculus.CBGroundResolutionBridge
import ContextCalculus.CBLocalPropositionalModel
import ContextCalculus.CBSourceProductionClosure
import ContextCalculus.CBSourceCanonicalOrder

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
open ContextCalculus.CBSourceLinearExtension
open ContextCalculus.CBSourceCanonicalOrder

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

/-- The local candidate model instantiated with the checked production-order
extension, rather than an unrelated ambient order on literals. -/
theorem SourceProductionClosed.context_canonical_raw_model
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (hbot : PClause.bot ∉ rawSet context.retained) :
    ∃ valuation : FLit → Prop,
      ∀ clause ∈ context.retained,
        ContextCalculus.sat valuation clause := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  exact
    ContextCalculus.CBSourceGroundResolutionBridge.SourceProductionClosed.context_raw_model
      closed context hcontext hbot

/-- The exact Bachmair–Ganzinger candidate valuation induced by KM's checked
production order satisfies every retained clause in the context. -/
theorem SourceProductionClosed.context_ordered_candidate_model
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (hbot : PClause.bot ∉ rawSet context.retained) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    ∀ clause ∈ context.retained,
      ContextCalculus.sat (OrdRes.Itrue (rawSet context.retained)) clause := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  exact local_raw_canonical_model context.retained
    (closed.localResolution context hcontext) hbot

/-- Every literal made true by the exact ordered candidate valuation has a
concrete retained producer whose selected occurrence is maximal under KM's
production order. -/
theorem ordered_candidate_true_has_production_provider
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (literal : FLit) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    OrdRes.Itrue (rawSet context.retained) literal →
      ∃ provider ∈ context.retained, ∃ index,
        provider.head[index]? = some literal ∧
        index ∈ (hyperOf decoded).order.maximalHeadIndices
          context.root provider.head := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  intro htrue
  obtain ⟨raw, hraw, hstrict, _, _⟩ :=
    (OrdRes.Itrue_def (rawSet context.retained) literal).mp htrue
  obtain ⟨provider, hprovider, hrawProvider⟩ :=
    (mem_rawSet_iff context.retained raw).mp hraw
  subst raw
  have hliteralHead : literal ∈ provider.head :=
    List.mem_toFinset.mp hstrict.1
  obtain ⟨index, hbound, hget⟩ :=
    List.mem_iff_getElem.mp hliteralHead
  have hindex : provider.head[index]? = some literal :=
    List.getElem?_eq_some_iff.mpr ⟨hbound, hget⟩
  refine ⟨provider, hprovider, index, hindex, ?_⟩
  apply canonical_max_is_production_maximal
    (hyperOf decoded).order context hcontext provider hprovider extension index
    literal hindex
  intro other hother
  have hotherSupport := retained_head_mem_ordered
    (hyperOf decoded).order context hcontext provider hprovider other hother
  have hliteralSupport := retained_head_mem_ordered
    (hyperOf decoded).order context hcontext provider hprovider literal
      hliteralHead
  rw [← supported_rank_le_iff extension
    ((extension.mem_linear_iff other).mpr hotherSupport)
    ((extension.mem_linear_iff literal).mpr hliteralSupport)]
  by_cases hequal : other = literal
  · subst other
    exact le_rfl
  · exact le_of_lt (hstrict.2.2 other
      (ContextCalculus.OrdRes.mem_lits.mpr
        (Or.inr (List.mem_toFinset.mpr hother))) hequal)

theorem ordered_candidate_true_has_provider_location
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (literal : FLit) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    OrdRes.Itrue (rawSet context.retained) literal →
      ∃ location,
        location ∈ CBSourceHyperClosure.maximalProvidersFor
          (hyperOf decoded).order context.root context.retained literal := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  intro htrue
  obtain ⟨provider, hprovider, headIndex, hhead, hmaximal⟩ :=
    ordered_candidate_true_has_production_provider context hcontext extension
      literal htrue
  obtain ⟨clauseIndex, hbound, hget⟩ :=
    List.mem_iff_getElem.mp hprovider
  have hproviderAt : context.retained[clauseIndex]? = some provider :=
    List.getElem?_eq_some_iff.mpr ⟨hbound, hget⟩
  refine ⟨(clauseIndex, headIndex), ?_⟩
  rw [CBSourceHyperClosure.mem_maximalProvidersFor_iff]
  exact ⟨hbound, provider, hproviderAt, hmaximal, hhead⟩

theorem ordered_candidate_true_body_has_provider_selection
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (body : List FLit) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    (∀ literal ∈ body,
      OrdRes.Itrue (rawSet context.retained) literal) →
      ∃ selection,
        selection ∈ CBSourceHyperClosure.providerSelections
          (hyperOf decoded).order context.root context.retained body := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  induction body with
  | nil =>
      intro _
      exact ⟨[], by simp [CBSourceHyperClosure.providerSelections,
        CBPredEnumeration.cartesianSelections]⟩
  | cons literal body ih =>
      intro htrue
      obtain ⟨location, hlocation⟩ :=
        ordered_candidate_true_has_provider_location context hcontext extension
          literal (htrue literal (by simp))
      obtain ⟨selection, hselection⟩ := ih (fun candidate hcandidate =>
        htrue candidate (by simp [hcandidate]))
      refine ⟨location :: selection, ?_⟩
      rw [CBSourceHyperClosure.mem_providerSelections_iff]
      simp only [List.map_cons, CBPredEnumeration.Selects]
      exact ⟨hlocation,
        (CBSourceHyperClosure.mem_providerSelections_iff _ _ _ _ _).mp
          hselection⟩

/-- For every source instance whose body is true in the exact ordered
candidate valuation, exhaustive production-provider enumeration reaches a raw
Hyper conclusion. If head normalization keeps that conclusion, terminal Hyper
closure supplies a retained strengthening of it. The `none` branch is the
equality-tautology case handled by the quotient-model bridge. -/
theorem SourceProductionClosed.ordered_candidate_hyper_step
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (sourceClause : FCL)
    (hsource : sourceClause ∈
      (liveOf decoded).production.source.ontology)
    (substitution : List (Int × FTerm))
    (hsubstitution : substitution ∈
      CBHyperClosure.substitutions (hyperOf decoded).order.orderedTerms
        sourceClause) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    (∀ literal ∈ (substCl substitution sourceClause).body,
      OrdRes.Itrue (rawSet context.retained) literal) →
      ∃ selection providers raw,
        selection ∈ CBSourceHyperClosure.providerSelections
          (hyperOf decoded).order context.root context.retained
          (substCl substitution sourceClause).body ∧
        CBHyperClosure.selectedProviders context.retained
          (substCl substitution sourceClause).body selection = some providers ∧
        CBHyperClosure.resolveProviders (substCl substitution sourceClause)
          providers = some raw ∧
        match CBLocalFactorClosureWire.normalizeGeneratedHead raw.head with
        | none => True
        | some filtered =>
            ∃ retained ∈ context.retained,
              CBProductionTrace.Strengthens retained { raw with head := filtered } := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  intro hbody
  let instantiated := substCl substitution sourceClause
  obtain ⟨selection, hselection⟩ :=
    ordered_candidate_true_body_has_provider_selection context hcontext
      extension instantiated.body hbody
  obtain ⟨providers, raw, hproviders, hraw⟩ :=
    CBSourceHyperClosure.hyperResolution_exists_of_mem_providerSelections
      (hyperOf decoded).order context.root context.retained instantiated
      selection hselection
  refine ⟨selection, providers, raw, hselection, hproviders, hraw, ?_⟩
  cases hnormal : CBLocalFactorClosureWire.normalizeGeneratedHead raw.head with
  | none => trivial
  | some filtered =>
      apply closed.hyper context hcontext { raw with head := filtered }
      simp only [CBSourceHyperClosure.hyperCandidates, List.mem_flatMap,
        List.mem_filterMap]
      refine ⟨sourceClause, hsource, substitution, hsubstitution, selection,
        hselection, ?_⟩
      simp [CBHyperClosure.hyperCandidate?, instantiated, hproviders, hraw,
        hnormal]

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
#print axioms SourceProductionClosed.context_canonical_raw_model
#print axioms SourceProductionClosed.context_ordered_candidate_model
#print axioms ordered_candidate_true_has_production_provider
#print axioms ordered_candidate_true_has_provider_location
#print axioms ordered_candidate_true_body_has_provider_selection
#print axioms SourceProductionClosed.ordered_candidate_hyper_step
#print axioms SourceProductionClosed.retained_head_equality_normal
#print axioms SourceProductionClosed.retained_factor_pair_covered
#print axioms SourceProductionClosed.retained_eq_pair_covered

end ContextCalculus.CBSourceGroundResolutionBridge
