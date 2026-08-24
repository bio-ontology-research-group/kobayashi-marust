import ContextCalculus.CBSourceGroundResolutionBridge
import ContextCalculus.CompletenessFO

/-!
# Equality-free source completeness from production CB closure

This closes the canonical-model argument before quotient equality is added.
It proves that the exact ordered candidate valuation satisfies every checked
source instance when the source and retained context are equality-free.
-/

namespace ContextCalculus.CBSourceEqualityFreeCompleteness

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CompletenessFO
open ContextCalculus.CBSourceRootPredClosure
open ContextCalculus.CBSourceProductionClosure
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceLinearExtension
open ContextCalculus.CBSourceCanonicalOrder
open ContextCalculus.CBSourceGroundResolutionBridge
open ContextCalculus.CBLocalPropositionalModel
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBSourceCanonicalClosure

theorem isP_substL (substitution : List (Int × FTerm))
    (literal : FLit) (h : IsP literal) : IsP (substL substitution literal) := by
  cases literal with
  | P predicate => cases predicate <;> trivial
  | eq left right => simp [IsP] at h
  | ineq left right => simp [IsP] at h

theorem eqFree_substCl (substitution : List (Int × FTerm))
    (clause : FCL) (hfree : EqFree clause) :
    EqFree (substCl substitution clause) := by
  constructor
  · intro literal hliteral
    simp only [substCl, List.mem_map] at hliteral
    obtain ⟨source, hsource, rfl⟩ := hliteral
    exact isP_substL substitution source (hfree.1 source hsource)
  · intro literal hliteral
    simp only [substCl, List.mem_map] at hliteral
    obtain ⟨source, hsource, rfl⟩ := hliteral
    exact isP_substL substitution source (hfree.2 source hsource)

theorem eqFree_resolvent (provider source : FCL) (literal : FLit)
    (hprovider : EqFree provider) (hsource : EqFree source) :
    EqFree (resolvent provider source literal) := by
  constructor
  · intro candidate hcandidate
    simp only [resolvent, List.mem_append] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · exact hprovider.1 candidate hcandidate
    · exact hsource.1 candidate (mem_without.mp hcandidate).1
  · intro candidate hcandidate
    simp only [resolvent, List.mem_append] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · exact hprovider.2 candidate (mem_without.mp hcandidate).1
    · exact hsource.2 candidate hcandidate

theorem resolveProviders_eqFree :
    ∀ {source providers conclusion},
      CBHyperClosure.resolveProviders source providers = some conclusion →
      EqFree source →
      (∀ selected ∈ providers, EqFree selected.2) →
      EqFree conclusion := by
  intro source providers
  induction providers generalizing source with
  | nil =>
      intro conclusion hresolve hsource _
      simp [CBHyperClosure.resolveProviders] at hresolve
      subst conclusion
      exact hsource
  | cons selected providers ih =>
      rcases selected with ⟨literal, provider⟩
      intro conclusion hresolve hsource hproviders
      have hprovider : EqFree provider :=
        hproviders (literal, provider) (by simp)
      have htail : ∀ selected ∈ providers, EqFree selected.2 := by
        intro selected hselected
        exact hproviders selected (by simp [hselected])
      by_cases hbody : literal ∈ source.body
      · have hliteralP := hsource.1 literal hbody
        cases literal with
        | P predicate =>
            have hhead : FLit.P predicate ∈ provider.head := by
              by_contra hnot
              simp [CBHyperClosure.resolveProviders, hbody, hnot] at hresolve
            simp only [CBHyperClosure.resolveProviders, hbody, hhead] at hresolve
            exact ih hresolve
              (eqFree_resolvent provider source (.P predicate) hprovider hsource)
              htail
        | eq left right => simp [IsP] at hliteralP
        | ineq left right => simp [IsP] at hliteralP
      · simp only [CBHyperClosure.resolveProviders, hbody] at hresolve
        exact ih hresolve hsource htail

theorem normalizeGeneratedHead_eq_self_of_isP (head : List FLit)
    (hfree : ∀ literal ∈ head, IsP literal) :
    CBLocalFactorClosureWire.normalizeGeneratedHead head = some head := by
  have hreflexive : head.any
      CBLocalFactorClosureWire.isReflexiveEquality = false := by
    apply List.any_eq_false.mpr
    intro literal hliteral
    have hp := hfree literal hliteral
    cases literal with
    | P predicate => simp [CBLocalFactorClosureWire.isReflexiveEquality]
    | eq left right => simp [IsP] at hp
    | ineq left right => simp [IsP] at hp
  have hfilter : head.filter (fun literal =>
      !CBLocalFactorClosureWire.isReflexiveInequality literal) = head := by
    apply List.filter_eq_self.mpr
    intro literal hliteral
    have hp := hfree literal hliteral
    cases literal with
    | P predicate => rfl
    | eq left right => simp [IsP] at hp
    | ineq left right => simp [IsP] at hp
  have hcomplement : CBLocalFactorClosureWire.hasEqualityComplement head =
      false := by
    apply List.any_eq_false.mpr
    intro literal hliteral
    have hp := hfree literal hliteral
    cases literal with
    | P predicate => simp [CBLocalFactorClosureWire.hasEqualityComplement]
    | eq left right => simp [IsP] at hp
    | ineq left right => simp [IsP] at hp
  simp [CBLocalFactorClosureWire.normalizeGeneratedHead,
    CBLocalFactorClosureWire.filterReflexiveHead, hreflexive, hfilter,
    hcomplement]

theorem SourceProductionClosed.ordered_candidate_source_instance_eqFree
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (hbot : PropRes.PClause.bot ∉ rawSet context.retained)
    (sourceClause : FCL)
    (hsource : sourceClause ∈
      (liveOf decoded).production.source.ontology)
    (hsourceFree : EqFree sourceClause)
    (hretainedFree : ∀ retained ∈ context.retained, EqFree retained)
    (substitution : List (Int × FTerm))
    (hsubstitution : substitution ∈
      CBHyperClosure.substitutions (hyperOf decoded).order.orderedTerms
        sourceClause) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    ContextCalculus.sat (OrdRes.Itrue (rawSet context.retained))
      (substCl substitution sourceClause) := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  rcases
      ContextCalculus.CBSourceGroundResolutionBridge.SourceProductionClosed.ordered_candidate_source_instance_or_tautology
        closed context hcontext extension hbot sourceClause hsource substitution
          hsubstitution with
    hsat | ⟨_, providers, raw, _, hproviders, hraw, hnone⟩
  · exact hsat
  · have hdecoded := CBHyperClosure.selectedProviders_sound
      context.retained hproviders
    have hprovidersFree : ∀ selected ∈ providers, EqFree selected.2 := by
      intro selected hselected
      exact hretainedFree selected.2 (hdecoded.2 selected hselected).1
    have hrawFree : EqFree raw := resolveProviders_eqFree hraw
      (eqFree_substCl substitution sourceClause hsourceFree) hprovidersFree
    have hsome := normalizeGeneratedHead_eq_self_of_isP raw.head hrawFree.2
    rw [hsome] at hnone
    contradiction

theorem SourceProductionClosed.context_source_instances_eqFree
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (hbot : PropRes.PClause.bot ∉ rawSet context.retained)
    (hsourceFree : ∀ sourceClause ∈
      (liveOf decoded).production.source.ontology, EqFree sourceClause)
    (hretainedFree : ∀ retained ∈ context.retained, EqFree retained) :
    letI := linearOrder extension
    letI := wellFoundedLT extension
    ∀ sourceClause ∈ (liveOf decoded).production.source.ontology,
      ∀ substitution ∈ CBHyperClosure.substitutions
          (hyperOf decoded).order.orderedTerms sourceClause,
        ContextCalculus.sat (OrdRes.Itrue (rawSet context.retained))
          (substCl substitution sourceClause) := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  intro sourceClause hsource substitution hsubstitution
  exact
    ContextCalculus.CBSourceEqualityFreeCompleteness.SourceProductionClosed.ordered_candidate_source_instance_eqFree
      closed context hcontext extension hbot sourceClause hsource
        (hsourceFree sourceClause hsource) hretainedFree substitution
        hsubstitution

theorem DecodedSourceCanonicalClosureDocument.all_context_source_instances_eqFree
    (decoded : DecodedSourceCanonicalClosureDocument)
    (hbot : ∀ context ∈
      (liveOf decoded.productionClosure).production.contexts,
      PropRes.PClause.bot ∉ rawSet context.retained)
    (hsourceFree : ∀ sourceClause ∈
      (liveOf decoded.productionClosure).production.source.ontology,
      EqFree sourceClause)
    (hretainedFree : ∀ context ∈
      (liveOf decoded.productionClosure).production.contexts,
      ∀ retained ∈ context.retained, EqFree retained) :
    ∀ context ∈ (liveOf decoded.productionClosure).production.contexts,
      let extension := decoded.extensionFor context.root
      letI := linearOrder extension
      letI := wellFoundedLT extension
      ∀ sourceClause ∈
          (liveOf decoded.productionClosure).production.source.ontology,
        ∀ substitution ∈ CBHyperClosure.substitutions
            (hyperOf decoded.productionClosure).order.orderedTerms sourceClause,
          ContextCalculus.sat (OrdRes.Itrue (rawSet context.retained))
            (substCl substitution sourceClause) := by
  intro context hcontext
  exact
    ContextCalculus.CBSourceEqualityFreeCompleteness.SourceProductionClosed.context_source_instances_eqFree
      decoded.production_closed context hcontext
        (decoded.extensionFor context.root) (hbot context hcontext) hsourceFree
        (hretainedFree context hcontext)

#print axioms eqFree_substCl
#print axioms resolveProviders_eqFree
#print axioms normalizeGeneratedHead_eq_self_of_isP
#print axioms SourceProductionClosed.ordered_candidate_source_instance_eqFree
#print axioms SourceProductionClosed.context_source_instances_eqFree
#print axioms DecodedSourceCanonicalClosureDocument.all_context_source_instances_eqFree

end ContextCalculus.CBSourceEqualityFreeCompleteness
