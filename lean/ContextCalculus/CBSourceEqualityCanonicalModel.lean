import ContextCalculus.CBSourceGroundResolutionBridge
import ContextCalculus.CompletenessTermRewriting

/-!
# Source-bound equality canonical model

This module begins the equality extension of the source canonical model.  It
first exposes, from the checked production snapshot alone, the orientation
invariant needed for terminating ordered rewriting: every non-reflexive
retained equality rewrites from a strictly greater term to a smaller term.
-/

namespace ContextCalculus.CBSourceEqualityCanonicalModel

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBFiniteTermOrderWire
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceProductionClosure
open ContextCalculus.CBSourceRootPredClosure
open ContextCalculus.CBSourceLiveInsertionDerivation
open ContextCalculus.CBProductionTraceWire
open ContextCalculus.CBSourceGroundResolutionBridge
open ContextCalculus.CBSourceLinearExtension
open ContextCalculus.CBSourceCanonicalOrder
open ContextCalculus.CBLocalPropositionalModel
open ContextCalculus.CBGroundEqualityBridge
open ContextCalculus.CBGroundResolutionBridge
open ContextCalculus.Eqv
open ContextCalculus.CBClauseShape

/-- Every normalized source body has exactly KM's supported positive-predicate
polarity.  The fact comes from the checked source binding, not an assumption of
the canonical-model theorem. -/
theorem source_clause_predicateBody
    {decoded : DecodedSourceRootPredClosureDocument}
    (sourceClause : FCL)
    (hsource : sourceClause ∈
      (liveOf decoded).production.source.ontology) :
    PredicateBody sourceClause :=
  (liveOf decoded).production.source.ontology_predicateBody
    sourceClause hsource

theorem source_instance_predicateBody
    {decoded : DecodedSourceRootPredClosureDocument}
    (sourceClause : FCL)
    (hsource : sourceClause ∈
      (liveOf decoded).production.source.ontology)
    (substitution : List (Int × FTerm)) :
    PredicateBody (substCl substitution sourceClause) :=
  predicateBody_substCl substitution sourceClause
    (source_clause_predicateBody sourceClause hsource)

/-- Retained clauses carry the same invariant as checked evidence in every
production context. -/
theorem retained_clause_predicateBody
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (clause : FCL) (hclause : clause ∈ context.retained) :
    PredicateBody clause :=
  context.retained_predicate_body clause hclause

/-- Ground atoms inherit the checked production extension through their unique
positive CB literal.  This is the polarity-aware order used for the equational
ordered-model bridge. -/
@[reducible] noncomputable def sourceGroundLinearOrder
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : LinearOrder GroundAtom := by
  letI : LinearOrder FLit := linearOrder extension
  exact LinearOrder.lift' literalOfGroundAtom literalOfGroundAtom_injective

theorem sourceGround_lt_wf
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    @WellFounded GroundAtom (sourceGroundLinearOrder context extension).lt := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  exact InvImage.wf literalOfGroundAtom wellFounded_lt

@[simp] theorem sourceGround_le_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (left right : GroundAtom) :
    letI : LinearOrder GroundAtom := sourceGroundLinearOrder context extension
    left ≤ right ↔
      letI : LinearOrder FLit := linearOrder extension
      literalOfGroundAtom left ≤ literalOfGroundAtom right := by
  rfl

@[simp] theorem sourceGround_lt_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (left right : GroundAtom) :
    letI : LinearOrder GroundAtom := sourceGroundLinearOrder context extension
    left < right ↔
      letI : LinearOrder FLit := linearOrder extension
      literalOfGroundAtom left < literalOfGroundAtom right := by
  rfl

/-- Every production context has the unique checked live-state context with
the same retained clauses and root-domain flag. -/
theorem exists_live_context_of_production_context
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts) :
    ∃ liveContext ∈ (liveOf decoded).contexts,
      liveContext.retained = context.retained ∧
        liveContext.rootDomain = context.root := by
  obtain ⟨index, hindexBound, hindexGet⟩ :=
    List.mem_iff_getElem.mp hcontext
  have hindexRange : index ∈
      List.range (liveOf decoded).production.contexts.length :=
    List.mem_range.mpr hindexBound
  rw [← (liveOf decoded).context_indices_exact] at hindexRange
  obtain ⟨liveContext, hlive, hliveIndex⟩ :=
    List.mem_map.mp hindexRange
  have hcontextAt :
      (liveOf decoded).production.contexts.get liveContext.contextIndex =
        context := by
    have hindexEq : liveContext.contextIndex.val = index := hliveIndex
    have hfinEq : liveContext.contextIndex = ⟨index, hindexBound⟩ :=
      Fin.ext hindexEq
    rw [hfinEq]
    exact hindexGet
  refine ⟨liveContext, hlive, ?_, ?_⟩
  · rw [liveContext.retained_eq, hcontextAt]
  · rw [← liveContext.root_eq, hcontextAt]

theorem self_mem_termAndSubterms (term : FTerm) :
    term ∈ termAndSubterms term := by
  cases term <;> simp [termAndSubterms]

theorem retained_literal_mem_ordered
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    (literal : FLit) (hliteral : literal ∈ clause.head) :
    literal ∈ (hyperOf decoded).order.orderedLiterals := by
  let order := (hyperOf decoded).order
  have hsource : literal ∈ sourceProductionLiterals (liveOf decoded).production := by
    unfold sourceProductionLiterals
    apply List.mem_eraseDups.mpr
    simp only [List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨context, hcontext, clause, hclause,
      by simp [clauseLiterals, hliteral]⟩
  have hfinset : literal ∈ order.orderedLiterals.toFinset := by
    rw [order.literals_exact]
    simpa using hsource
  simpa using hfinset

theorem retained_equality_term_mem_ordered
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    (left right : FTerm) (hequality : FLit.eq left right ∈ clause.head) :
    left ∈ (hyperOf decoded).order.orderedTerms ∧
      right ∈ (hyperOf decoded).order.orderedTerms := by
  let order := (hyperOf decoded).order
  have hsourceLeft : left ∈ sourceProductionTerms (liveOf decoded).production := by
    unfold sourceProductionTerms
    apply List.mem_eraseDups.mpr
    simp only [List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨context, hcontext, clause, hclause, by
      simp only [clauseTerms, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨.eq left right, hequality, by
        simp only [literalTerms, List.mem_append]
        exact Or.inl (self_mem_termAndSubterms left)⟩⟩
  have hsourceRight : right ∈ sourceProductionTerms (liveOf decoded).production := by
    unfold sourceProductionTerms
    apply List.mem_eraseDups.mpr
    simp only [List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨context, hcontext, clause, hclause, by
      simp only [clauseTerms, List.mem_append, List.mem_flatMap]
      exact Or.inr ⟨.eq left right, hequality, by
        simp only [literalTerms, List.mem_append]
        exact Or.inr (self_mem_termAndSubterms right)⟩⟩
  constructor
  · have : left ∈ order.orderedTerms.toFinset := by
      rw [order.terms_exact]
      simpa using hsourceLeft
    simpa using this
  · have : right ∈ order.orderedTerms.toFinset := by
      rw [order.terms_exact]
      simpa using hsourceRight
    simpa using this

/-- The checked source snapshot turns every non-reflexive retained equality
into a strict decrease in KM's exact production term order. -/
theorem retained_equality_strictly_decreases
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    (left right : FTerm) (hequality : FLit.eq left right ∈ clause.head)
    (hne : left ≠ right) :
    (hyperOf decoded).order.termLt right left = true := by
  let order := (hyperOf decoded).order
  have hliteral : FLit.eq left right ∈ order.orderedLiterals :=
    retained_literal_mem_ordered context hcontext clause hclause
      (.eq left right) hequality
  obtain ⟨hleft, _⟩ :=
    retained_equality_term_mem_ordered context hcontext clause hclause
      left right hequality
  exact order.strictly_oriented_of_ne hleft
    (order.equality_oriented_of_mem hliteral) hne

/-- Productive equality rewriting for one exact ordered candidate valuation.
The relation is written `smaller <- larger`, matching Lean's convention for a
well-founded relation. -/
def ProductiveEqualityRewrite
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (smaller larger : FTerm) : Prop :=
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  OrdRes.Itrue (rawSet context.retained) (.eq larger smaller)

theorem productiveEqualityRewrite_terms_mem_ordered
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {smaller larger : FTerm}
    (hrewrite : ProductiveEqualityRewrite context extension smaller larger) :
    smaller ∈ (hyperOf decoded).order.orderedTerms ∧
      larger ∈ (hyperOf decoded).order.orderedTerms := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  have htrue : OrdRes.Itrue (rawSet context.retained) (.eq larger smaller) := by
    simpa [ProductiveEqualityRewrite] using hrewrite
  obtain ⟨provider, hprovider, _, hhead, _, _, _⟩ :=
    ordered_candidate_true_has_production_provider context hcontext extension
      (.eq larger smaller) htrue
  have hequality : FLit.eq larger smaller ∈ provider.head := by
    obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hhead
    exact List.mem_iff_getElem.mpr ⟨_, hbound, hget⟩
  obtain ⟨hlarger, hsmaller⟩ := retained_equality_term_mem_ordered
    context hcontext provider hprovider larger smaller hequality
  exact ⟨hsmaller, hlarger⟩

theorem productiveEqualityRewrite_decreases
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {smaller larger : FTerm}
    (hrewrite : ProductiveEqualityRewrite context extension smaller larger) :
    (hyperOf decoded).order.termLt smaller larger = true := by
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  have htrue : OrdRes.Itrue (rawSet context.retained) (.eq larger smaller) := by
    simpa [ProductiveEqualityRewrite] using hrewrite
  obtain ⟨provider, hprovider, index, hhead, _, _, _⟩ :=
    ordered_candidate_true_has_production_provider context hcontext extension
      (.eq larger smaller) htrue
  have hequality : FLit.eq larger smaller ∈ provider.head := by
    obtain ⟨hbound, hget⟩ := List.getElem?_eq_some_iff.mp hhead
    exact List.mem_iff_getElem.mpr ⟨index, hbound, hget⟩
  have hne : larger ≠ smaller := by
    intro hequal
    subst smaller
    exact
      (ContextCalculus.CBSourceGroundResolutionBridge.SourceProductionClosed.retained_head_equality_normal
        closed context hcontext provider hprovider).1 larger hequality
  exact retained_equality_strictly_decreases context hcontext provider hprovider
    larger smaller hequality hne

theorem productiveEqualityRewrite_wellFounded
    {decoded : DecodedSourceRootPredClosureDocument}
    (closed : SourceProductionClosed decoded)
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    WellFounded (ProductiveEqualityRewrite context extension) := by
  let order := (hyperOf decoded).order
  exact Subrelation.wf
    (fun {_ _} hrewrite => by
      have hdecrease := productiveEqualityRewrite_decreases closed context
        hcontext extension hrewrite
      simpa [DecodedSourceFiniteOrder.termLt] using hdecrease)
    (measure order.termRank).wf

/-- Equality on the source-model carrier is the equivalence closure of KM's
productive equalities.  It deliberately does not close under the syntactic
Skolem application constructor: Skolem functions are absent from the original
OWL source signature and are reconstructed only after a source model exists. -/
inductive ProductiveEquivalence
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : FTerm → FTerm → Prop where
  | productive {smaller larger}
      (h : ProductiveEqualityRewrite context extension smaller larger) :
      ProductiveEquivalence context extension larger smaller
  | refl (term) : ProductiveEquivalence context extension term term
  | symm {left right} : ProductiveEquivalence context extension left right →
      ProductiveEquivalence context extension right left
  | trans {left middle right} :
      ProductiveEquivalence context extension left middle →
      ProductiveEquivalence context extension middle right →
      ProductiveEquivalence context extension left right

def productiveEquivalenceSetoid
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : Setoid FTerm where
  r := ProductiveEquivalence context extension
  iseqv := {
    refl := ProductiveEquivalence.refl
    symm := ProductiveEquivalence.symm
    trans := ProductiveEquivalence.trans }

/-- Canonical reduction inside a productive equality class. Unlike the raw
productive edges, this relation also orients equalities justified transitively
or by a semantically tautological Eq critical pair. -/
def ProductiveClassRewrite
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (smaller larger : FTerm) : Prop :=
  ProductiveEquivalence context extension smaller larger ∧
    smaller ∈ (hyperOf decoded).order.orderedTerms ∧
    larger ∈ (hyperOf decoded).order.orderedTerms ∧
    (hyperOf decoded).order.termLt smaller larger = true

theorem productiveClassRewrite_wellFounded
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    WellFounded (ProductiveClassRewrite context extension) := by
  let order := (hyperOf decoded).order
  exact Subrelation.wf
    (fun {_ _} hrewrite => by
      simpa [DecodedSourceFiniteOrder.termLt] using hrewrite.2.2.2)
    (measure order.termRank).wf

theorem productiveClassRewrite_directlyJoinable
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    TermRewriting.DirectlyJoinable
      (ProductiveClassRewrite context extension) := by
  intro source left right hleft hright
  by_cases hequal : left = right
  · exact Or.inl hequal
  · have hrankNe : (hyperOf decoded).order.termRank left ≠
        (hyperOf decoded).order.termRank right := by
      intro hrank
      exact hequal (List.idxOf_inj hleft.2.1 |>.mp hrank)
    rcases lt_or_gt_of_ne hrankNe with hlt | hgt
    · exact Or.inr (Or.inl ⟨
        ProductiveEquivalence.trans hleft.1
          (ProductiveEquivalence.symm hright.1),
        hleft.2.1, hright.2.1,
        by simpa [DecodedSourceFiniteOrder.termLt] using hlt⟩)
    · exact Or.inr (Or.inr ⟨
        ProductiveEquivalence.trans hright.1
          (ProductiveEquivalence.symm hleft.1),
        hright.2.1, hleft.2.1,
        by simpa [DecodedSourceFiniteOrder.termLt] using hgt⟩)

noncomputable def productiveClassNormalForm
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : FTerm → FTerm :=
  TermRewriting.normalForm (ProductiveClassRewrite context extension)
    (productiveClassRewrite_wellFounded context extension)

@[simp] theorem productiveClassNormalForm_idempotent
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (term : FTerm) :
    productiveClassNormalForm context extension
        (productiveClassNormalForm context extension term) =
      productiveClassNormalForm context extension term :=
  TermRewriting.normalForm_idempotent
    (ProductiveClassRewrite context extension)
    (productiveClassRewrite_wellFounded context extension) term

theorem productiveClassNormalForm_mem_ordered
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (term : FTerm)
    (hterm : term ∈ (hyperOf decoded).order.orderedTerms) :
    productiveClassNormalForm context extension term ∈
      (hyperOf decoded).order.orderedTerms :=
  TermRewriting.normalForm_preserves
    (ProductiveClassRewrite context extension)
    (productiveClassRewrite_wellFounded context extension)
    (fun candidate => candidate ∈ (hyperOf decoded).order.orderedTerms)
    (fun {_ _} hrewrite _ => hrewrite.2.1) term hterm

theorem productiveClassNormalForm_equivalent
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (term : FTerm) :
    ProductiveEquivalence context extension term
      (productiveClassNormalForm context extension term) := by
  have hpath := TermRewriting.reflTransGen_normalForm
    (ProductiveClassRewrite context extension)
    (productiveClassRewrite_wellFounded context extension) term
  refine Relation.ReflTransGen.trans_induction_on
    (motive := fun {left right} _ =>
      ProductiveEquivalence context extension left right) hpath ?_ ?_ ?_
  · exact fun candidate => ProductiveEquivalence.refl candidate
  · intro left right hstep
    exact ProductiveEquivalence.symm hstep.1
  · intro left middle right _ _ hleft hright
    exact ProductiveEquivalence.trans hleft hright

theorem productiveClassNormalForm_eq_of_equivalent
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {left right : FTerm}
    (hequivalent : ProductiveEquivalence context extension left right)
    (hleft : left ∈ (hyperOf decoded).order.orderedTerms)
    (hright : right ∈ (hyperOf decoded).order.orderedTerms) :
    productiveClassNormalForm context extension left =
      productiveClassNormalForm context extension right := by
  by_cases hequal : left = right
  · subst right
    rfl
  · have hrankNe : (hyperOf decoded).order.termRank left ≠
        (hyperOf decoded).order.termRank right := by
      intro hrank
      exact hequal (List.idxOf_inj hleft |>.mp hrank)
    rcases lt_or_gt_of_ne hrankNe with hlt | hgt
    · exact TermRewriting.normalForm_eq_of_step
        (ProductiveClassRewrite context extension)
        (productiveClassRewrite_wellFounded context extension)
        (productiveClassRewrite_directlyJoinable context extension)
        ⟨hequivalent, hleft, hright,
          by simpa [DecodedSourceFiniteOrder.termLt] using hlt⟩
    · exact (TermRewriting.normalForm_eq_of_step
        (ProductiveClassRewrite context extension)
        (productiveClassRewrite_wellFounded context extension)
        (productiveClassRewrite_directlyJoinable context extension)
        ⟨ProductiveEquivalence.symm hequivalent, hright, hleft,
          by simpa [DecodedSourceFiniteOrder.termLt] using hgt⟩).symm

theorem productiveEquivalence_eq_or_mem_ordered
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {left right : FTerm}
    (hequivalent : ProductiveEquivalence context extension left right) :
    left = right ∨
      (left ∈ (hyperOf decoded).order.orderedTerms ∧
        right ∈ (hyperOf decoded).order.orderedTerms) := by
  induction hequivalent with
  | productive hrewrite =>
      obtain ⟨hsmaller, hlarger⟩ :=
        productiveEqualityRewrite_terms_mem_ordered context hcontext extension
          hrewrite
      exact Or.inr ⟨hlarger, hsmaller⟩
  | refl term => exact Or.inl rfl
  | symm hequivalent ih =>
      rcases ih with hequal | ⟨hleft, hright⟩
      · exact Or.inl hequal.symm
      · exact Or.inr ⟨hright, hleft⟩
  | trans hleft hright ihleft ihright =>
      rcases ihleft with hequalLeft | ⟨hfirst, hmiddle⟩
      · subst_vars
        exact ihright
      · rcases ihright with hequalRight | ⟨_, hlast⟩
        · subst_vars
          exact Or.inr ⟨hfirst, hmiddle⟩
        · exact Or.inr ⟨hfirst, hlast⟩

theorem productiveClassNormalForm_eq_of_equivalent_any
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {left right : FTerm}
    (hequivalent : ProductiveEquivalence context extension left right) :
    productiveClassNormalForm context extension left =
      productiveClassNormalForm context extension right := by
  rcases productiveEquivalence_eq_or_mem_ordered context hcontext extension
      hequivalent with hequal | ⟨hleft, hright⟩
  · subst right
    rfl
  · exact productiveClassNormalForm_eq_of_equivalent context extension
      hequivalent hleft hright

abbrev ProductiveSourceQuotient
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : Type :=
  Quotient (productiveEquivalenceSetoid context extension)

def sourceQuotientTerm
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (term : FTerm) :
    ProductiveSourceQuotient context extension := Quotient.mk _ term

/-- Canonical predicate extension: evaluate the exact ordered candidate only
at the unique normal-form representative of an equality class. -/
noncomputable def normalSourceConceptHolds
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (concept : Nat) :
    ProductiveSourceQuotient context extension → Prop :=
  Quotient.lift
    (fun term =>
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.concept concept
          (productiveClassNormalForm context extension term))))
    (by
      intro left right hequivalent
      apply propext
      dsimp only
      rw [productiveClassNormalForm_eq_of_equivalent_any context hcontext
        extension hequivalent])

noncomputable def normalSourceRoleHolds
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (role : Nat) :
    ProductiveSourceQuotient context extension →
      ProductiveSourceQuotient context extension → Prop :=
  Quotient.lift₂
    (fun source target =>
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.role role
          (productiveClassNormalForm context extension source)
          (productiveClassNormalForm context extension target))))
    (by
      intro source target source' target' hsource htarget
      apply propext
      dsimp only
      rw [productiveClassNormalForm_eq_of_equivalent_any context hcontext
          extension hsource,
        productiveClassNormalForm_eq_of_equivalent_any context hcontext
          extension htarget])

noncomputable def normalProductiveSourceInterpretation
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    Eqv.Interp (ProductiveSourceQuotient context extension) Nat Nat Nat where
  c := normalSourceConceptHolds context hcontext extension
  r := normalSourceRoleHolds context hcontext extension
  nm := fun individual => sourceQuotientTerm context extension (.const individual)

noncomputable def normalSourceLiteralValuation
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : FLit → Prop
  | .P (.concept concept term) =>
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.concept concept
          (productiveClassNormalForm context extension term)))
  | .P (.role role source target) =>
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.role role
          (productiveClassNormalForm context extension source)
          (productiveClassNormalForm context extension target)))
  | .eq left right => ProductiveEquivalence context extension left right
  | .ineq left right => ¬ ProductiveEquivalence context extension left right

/-- Rejected generated heads are tautological in the canonical productive
equality valuation, including both reflexive equalities and complementary
equality/disequality pairs. -/
theorem normalSourceLiteralValuation_sat_of_normalizeGeneratedHead_none
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (clause : FCL)
    (hnone : CBLocalFactorClosureWire.normalizeGeneratedHead clause.head = none) :
    ContextCalculus.sat (normalSourceLiteralValuation context extension) clause := by
  intro _
  cases hfilter : CBLocalFactorClosureWire.filterReflexiveHead clause.head with
  | none =>
      unfold CBLocalFactorClosureWire.filterReflexiveHead at hfilter
      by_cases hany : clause.head.any
          CBLocalFactorClosureWire.isReflexiveEquality = true
      · obtain ⟨literal, hliteral, hreflexive⟩ := List.any_eq_true.mp hany
        cases literal with
        | P predicate =>
            simp [CBLocalFactorClosureWire.isReflexiveEquality] at hreflexive
        | ineq left right =>
            simp [CBLocalFactorClosureWire.isReflexiveEquality] at hreflexive
        | eq left right =>
            simp only [CBLocalFactorClosureWire.isReflexiveEquality,
              decide_eq_true_eq] at hreflexive
            subst right
            exact ⟨.eq left left, hliteral, ProductiveEquivalence.refl left⟩
      · simp [hany] at hfilter
  | some filtered =>
      have hfiltered : filtered = clause.head.filter fun literal =>
          !CBLocalFactorClosureWire.isReflexiveInequality literal := by
        unfold CBLocalFactorClosureWire.filterReflexiveHead at hfilter
        split at hfilter
        · contradiction
        next _ => exact Option.some.inj hfilter |>.symm
      have hcomplement :
          CBLocalFactorClosureWire.hasEqualityComplement filtered = true := by
        by_contra hfalse
        have hfalse' :
            CBLocalFactorClosureWire.hasEqualityComplement filtered = false :=
          Bool.eq_false_of_not_eq_true hfalse
        simp [CBLocalFactorClosureWire.normalizeGeneratedHead, hfilter,
          hfalse'] at hnone
      obtain ⟨literal, hliteral, hpaired⟩ := List.any_eq_true.mp hcomplement
      cases literal with
      | P predicate =>
          simp [CBLocalFactorClosureWire.hasEqualityComplement] at hpaired
      | ineq left right =>
          simp [CBLocalFactorClosureWire.hasEqualityComplement] at hpaired
      | eq left right =>
          have hequality : .eq left right ∈ clause.head := by
            rw [hfiltered, List.mem_filter] at hliteral
            exact hliteral.1
          have hinequalityFiltered : .ineq left right ∈ filtered := by
            simpa [CBLocalFactorClosureWire.hasEqualityComplement] using hpaired
          have hinequality : .ineq left right ∈ clause.head := by
            rw [hfiltered, List.mem_filter] at hinequalityFiltered
            exact hinequalityFiltered.1
          by_cases hequal : ProductiveEquivalence context extension left right
          · exact ⟨.eq left right, hequality, hequal⟩
          · exact ⟨.ineq left right, hinequality, hequal⟩

@[simp] theorem normalSourceConceptHolds_mk
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (concept : Nat) (term : FTerm) :
    normalSourceConceptHolds context hcontext extension concept
        (sourceQuotientTerm context extension term) ↔
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.concept concept
          (productiveClassNormalForm context extension term))) :=
  Iff.rfl

@[simp] theorem normalSourceRoleHolds_mk
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (hcontext : context ∈ (liveOf decoded).production.contexts)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (role : Nat)
    (source target : FTerm) :
    normalSourceRoleHolds context hcontext extension role
        (sourceQuotientTerm context extension source)
        (sourceQuotientTerm context extension target) ↔
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.role role
          (productiveClassNormalForm context extension source)
          (productiveClassNormalForm context extension target))) :=
  Iff.rfl

def sourceConceptHolds
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (concept : Nat)
    (element : ProductiveSourceQuotient context extension) : Prop :=
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  ∃ term, sourceQuotientTerm context extension term = element ∧
    OrdRes.Itrue (rawSet context.retained) (.P (.concept concept term))

def sourceRoleHolds
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (role : Nat)
    (source target : ProductiveSourceQuotient context extension) : Prop :=
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  ∃ sourceTerm targetTerm,
    sourceQuotientTerm context extension sourceTerm = source ∧
    sourceQuotientTerm context extension targetTerm = target ∧
    OrdRes.Itrue (rawSet context.retained)
      (.P (.role role sourceTerm targetTerm))

theorem sourceConceptHolds_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (concept : Nat) (term : FTerm) :
    sourceConceptHolds context extension concept
        (sourceQuotientTerm context extension term) ↔
      ∃ witness,
        ProductiveEquivalence context extension witness term ∧
        letI : LinearOrder FLit := linearOrder extension
        letI : WellFoundedLT FLit := wellFoundedLT extension
        OrdRes.Itrue (rawSet context.retained)
          (.P (.concept concept witness)) := by
  simp only [sourceConceptHolds]
  constructor
  · rintro ⟨witness, hequal, htrue⟩
    exact ⟨witness, Quotient.eq.mp hequal, htrue⟩
  · rintro ⟨witness, hequal, htrue⟩
    exact ⟨witness, Quotient.sound hequal, htrue⟩

theorem sourceRoleHolds_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (role : Nat) (source target : FTerm) :
    sourceRoleHolds context extension role
        (sourceQuotientTerm context extension source)
        (sourceQuotientTerm context extension target) ↔
      ∃ sourceWitness targetWitness,
        ProductiveEquivalence context extension sourceWitness source ∧
        ProductiveEquivalence context extension targetWitness target ∧
        letI : LinearOrder FLit := linearOrder extension
        letI : WellFoundedLT FLit := wellFoundedLT extension
        OrdRes.Itrue (rawSet context.retained)
          (.P (.role role sourceWitness targetWitness)) := by
  simp only [sourceRoleHolds]
  constructor
  · rintro ⟨sourceWitness, targetWitness, hsource, htarget, htrue⟩
    exact ⟨sourceWitness, targetWitness, Quotient.eq.mp hsource,
      Quotient.eq.mp htarget, htrue⟩
  · rintro ⟨sourceWitness, targetWitness, hsource, htarget, htrue⟩
    exact ⟨sourceWitness, targetWitness, Quotient.sound hsource,
      Quotient.sound htarget, htrue⟩

/-- Ground presentation of the source quotient.  Unlike the earlier
Skolem-congruence draft, this relation is exactly the equality structure needed
by `Eqv.congruenceModel` for the original source signature. -/
noncomputable def productiveSourceGroundValuation
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    Eqv.GAtom Nat Nat FTerm → Prop
  | .con concept term => sourceConceptHolds context extension concept
      (sourceQuotientTerm context extension term)
  | .rol role source target => sourceRoleHolds context extension role
      (sourceQuotientTerm context extension source)
      (sourceQuotientTerm context extension target)
  | .eqa left right => ProductiveEquivalence context extension left right

theorem productiveSourceGroundValuation_respectsEq
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    Eqv.RespectsEq (productiveSourceGroundValuation context extension) := by
  constructor
  · exact ProductiveEquivalence.refl
  · exact ProductiveEquivalence.symm
  · exact ProductiveEquivalence.trans
  · intro concept left right hequal hconcept
    change sourceConceptHolds context extension concept
      (sourceQuotientTerm context extension right)
    change sourceConceptHolds context extension concept
      (sourceQuotientTerm context extension left) at hconcept
    have hquot : sourceQuotientTerm context extension left =
        sourceQuotientTerm context extension right := Quotient.sound hequal
    rwa [hquot] at hconcept
  · intro role left right target hequal hrole
    change sourceRoleHolds context extension role
      (sourceQuotientTerm context extension right)
      (sourceQuotientTerm context extension target)
    change sourceRoleHolds context extension role
      (sourceQuotientTerm context extension left)
      (sourceQuotientTerm context extension target) at hrole
    have hquot : sourceQuotientTerm context extension left =
        sourceQuotientTerm context extension right := Quotient.sound hequal
    rwa [hquot] at hrole
  · intro role source left right hequal hrole
    change sourceRoleHolds context extension role
      (sourceQuotientTerm context extension source)
      (sourceQuotientTerm context extension right)
    change sourceRoleHolds context extension role
      (sourceQuotientTerm context extension source)
      (sourceQuotientTerm context extension left) at hrole
    have hquot : sourceQuotientTerm context extension left =
        sourceQuotientTerm context extension right := Quotient.sound hequal
    rwa [hquot] at hrole

/-- Candidate interpretation of the original source signature.  Application
is intentionally absent; existential witness functions are reconstructed by
`CBEqEncoding.extendModel` only after this interpretation is shown to model
the source ontology. -/
noncomputable def productiveSourceInterpretation
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    Eqv.Interp (ProductiveSourceQuotient context extension) Nat Nat Nat where
  c := sourceConceptHolds context extension
  r := sourceRoleHolds context extension
  nm := fun individual => sourceQuotientTerm context extension (.const individual)

/-- The same source interpretation at the exact finite signature carried by
the checked frontend binding. -/
noncomputable def productiveBoundedSourceInterpretation
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    Eqv.Interp (ProductiveSourceQuotient context extension)
      (Fin (liveOf decoded).production.bounds.concepts)
      (Fin (liveOf decoded).production.bounds.roles)
      (Fin (liveOf decoded).production.bounds.individuals) where
  c := fun concept => sourceConceptHolds context extension concept.val
  r := fun role => sourceRoleHolds context extension role.val
  nm := fun individual =>
    sourceQuotientTerm context extension (.const individual.val)

theorem sourceQuotientTerm_productive_eq
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {smaller larger : FTerm}
    (hrewrite : ProductiveEqualityRewrite context extension smaller larger) :
    sourceQuotientTerm context extension larger =
      sourceQuotientTerm context extension smaller := by
  exact Quotient.sound (ProductiveEquivalence.productive hrewrite)

/-- Congruence generated by productive equalities.  KM need not rewrite inside
function terms operationally, but every first-order model must interpret equal
arguments identically; the `app` constructor supplies exactly that semantic
closure. -/
inductive ProductiveCongruence
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : FTerm → FTerm → Prop where
  | productive {smaller larger}
      (h : ProductiveEqualityRewrite context extension smaller larger) :
      ProductiveCongruence context extension larger smaller
  | app (function) {left right} :
      ProductiveCongruence context extension left right →
      ProductiveCongruence context extension (.app function left) (.app function right)
  | refl (term) : ProductiveCongruence context extension term term
  | symm {left right} : ProductiveCongruence context extension left right →
      ProductiveCongruence context extension right left
  | trans {left middle right} :
      ProductiveCongruence context extension left middle →
      ProductiveCongruence context extension middle right →
      ProductiveCongruence context extension left right

def productiveCongruenceSetoid
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : Setoid FTerm where
  r := ProductiveCongruence context extension
  iseqv := {
    refl := ProductiveCongruence.refl
    symm := ProductiveCongruence.symm
    trans := ProductiveCongruence.trans }

abbrev ProductiveQuotient
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : Type :=
  Quotient (productiveCongruenceSetoid context extension)

def quotientTerm
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (term : FTerm) :
    ProductiveQuotient context extension := Quotient.mk _ term

/-- Unary application descends to productive equality classes by semantic
function congruence. -/
def quotientApp
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (function : Nat)
    (element : ProductiveQuotient context extension) :
    ProductiveQuotient context extension :=
  Quotient.map (.app function)
    (fun _ _ hequal => ProductiveCongruence.app function hequal) element

theorem quotientTerm_productive_eq
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    {smaller larger : FTerm}
    (hrewrite : ProductiveEqualityRewrite context extension smaller larger) :
    quotientTerm context extension larger =
      quotientTerm context extension smaller := by
  exact Quotient.sound (ProductiveCongruence.productive hrewrite)

def productiveConceptHolds
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (concept : Nat)
    (element : ProductiveQuotient context extension) : Prop :=
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  ∃ term, quotientTerm context extension term = element ∧
    OrdRes.Itrue (rawSet context.retained) (.P (.concept concept term))

def productiveRoleHolds
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (role : Nat)
    (source target : ProductiveQuotient context extension) : Prop :=
  letI : LinearOrder FLit := linearOrder extension
  letI : WellFoundedLT FLit := wellFoundedLT extension
  ∃ sourceTerm targetTerm,
    quotientTerm context extension sourceTerm = source ∧
    quotientTerm context extension targetTerm = target ∧
    OrdRes.Itrue (rawSet context.retained)
      (.P (.role role sourceTerm targetTerm))

theorem productiveConceptHolds_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (concept : Nat) (term : FTerm) :
    productiveConceptHolds context extension concept
        (quotientTerm context extension term) ↔
      ∃ witness,
        ProductiveCongruence context extension witness term ∧
        letI : LinearOrder FLit := linearOrder extension
        letI : WellFoundedLT FLit := wellFoundedLT extension
        OrdRes.Itrue (rawSet context.retained)
          (.P (.concept concept witness)) := by
  simp only [productiveConceptHolds]
  constructor
  · rintro ⟨witness, hequal, htrue⟩
    exact ⟨witness, Quotient.eq.mp hequal, htrue⟩
  · rintro ⟨witness, hequal, htrue⟩
    exact ⟨witness, Quotient.sound hequal, htrue⟩

theorem productiveRoleHolds_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (role : Nat) (source target : FTerm) :
    productiveRoleHolds context extension role
        (quotientTerm context extension source)
        (quotientTerm context extension target) ↔
      ∃ sourceWitness targetWitness,
        ProductiveCongruence context extension sourceWitness source ∧
        ProductiveCongruence context extension targetWitness target ∧
        letI : LinearOrder FLit := linearOrder extension
        letI : WellFoundedLT FLit := wellFoundedLT extension
        OrdRes.Itrue (rawSet context.retained)
          (.P (.role role sourceWitness targetWitness)) := by
  simp only [productiveRoleHolds]
  constructor
  · rintro ⟨sourceWitness, targetWitness, hsource, htarget, htrue⟩
    exact ⟨sourceWitness, targetWitness, Quotient.eq.mp hsource,
      Quotient.eq.mp htarget, htrue⟩
  · rintro ⟨sourceWitness, targetWitness, hsource, htarget, htrue⟩
    exact ⟨sourceWitness, targetWitness, Quotient.sound hsource,
      Quotient.sound htarget, htrue⟩

/-- The first-order equality model induced by the exact candidate valuation.
Predicate extensions are the congruence closure of productive predicate facts;
equality itself is genuine quotient equality. -/
noncomputable def productiveQuotientModel
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    TModel (ProductiveQuotient context extension) where
  conc := productiveConceptHolds context extension
  rol := productiveRoleHolds context extension
  const := fun individual => quotientTerm context extension (.const individual)
  fn := quotientApp context extension

def quotientAssignment
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    Int → ProductiveQuotient context extension :=
  fun variableIndex => quotientTerm context extension (.var variableIndex)

/-- With congruence-closed application, model evaluation preserves the source
term itself.  The name is retained to keep downstream theorem statements
stable while replacing the former representative-based draft. -/
def quotientNormalizedTerm
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : FTerm → FTerm
  | term => term

@[simp] theorem productiveQuotientModel_evalT
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (term : FTerm) :
    (productiveQuotientModel context extension).evalT
        (quotientAssignment context extension) term =
      quotientTerm context extension
        (quotientNormalizedTerm context extension term) := by
  induction term with
  | var variableIndex => rfl
  | const individual => rfl
  | app function argument ih =>
      change quotientApp context extension function
        ((productiveQuotientModel context extension).evalT
          (quotientAssignment context extension) argument) = _
      rw [ih]
      rfl

theorem productiveQuotientModel_concept_of_true
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (concept : Nat) (term : FTerm)
    (htrue :
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.concept concept
          (quotientNormalizedTerm context extension term)))) :
    (productiveQuotientModel context extension).evalL
      (quotientAssignment context extension) (.P (.concept concept term)) := by
  rw [TModel.evalL, productiveQuotientModel_evalT]
  change productiveConceptHolds context extension concept
    (quotientTerm context extension
      (quotientNormalizedTerm context extension term))
  simp only [productiveConceptHolds]
  exact ⟨quotientNormalizedTerm context extension term, rfl, htrue⟩

theorem productiveQuotientModel_role_of_true
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (role : Nat)
    (source target : FTerm)
    (htrue :
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.P (.role role
          (quotientNormalizedTerm context extension source)
          (quotientNormalizedTerm context extension target)))) :
    (productiveQuotientModel context extension).evalL
      (quotientAssignment context extension)
      (.P (.role role source target)) := by
  rw [TModel.evalL, productiveQuotientModel_evalT,
    productiveQuotientModel_evalT]
  change productiveRoleHolds context extension role
    (quotientTerm context extension
      (quotientNormalizedTerm context extension source))
    (quotientTerm context extension
      (quotientNormalizedTerm context extension target))
  simp only [productiveRoleHolds]
  exact ⟨quotientNormalizedTerm context extension source,
    quotientNormalizedTerm context extension target, rfl, rfl, htrue⟩

@[simp] theorem productiveQuotientModel_eval_eq
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (left right : FTerm) :
    (productiveQuotientModel context extension).evalL
        (quotientAssignment context extension) (.eq left right) ↔
      ProductiveCongruence context extension
        (quotientNormalizedTerm context extension left)
        (quotientNormalizedTerm context extension right) := by
  rw [TModel.evalL, productiveQuotientModel_evalT,
    productiveQuotientModel_evalT]
  exact Quotient.eq

theorem productiveQuotientModel_equality_of_true
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (left right : FTerm)
    (htrue :
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained)
        (.eq (quotientNormalizedTerm context extension left)
          (quotientNormalizedTerm context extension right))) :
    (productiveQuotientModel context extension).evalL
      (quotientAssignment context extension) (.eq left right) := by
  rw [productiveQuotientModel_eval_eq]
  exact ProductiveCongruence.productive (by
    simpa [ProductiveEqualityRewrite] using htrue)

@[simp] theorem productiveQuotientModel_eval_ineq
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (left right : FTerm) :
    (productiveQuotientModel context extension).evalL
        (quotientAssignment context extension) (.ineq left right) ↔
      ¬ ProductiveCongruence context extension
        (quotientNormalizedTerm context extension left)
        (quotientNormalizedTerm context extension right) := by
  rw [TModel.evalL, productiveQuotientModel_evalT,
    productiveQuotientModel_evalT]
  exact not_congr Quotient.eq

/-- Ground valuation presented by the quotient model.  Terms are first mapped
to the exact representatives used by KM's unary function interpretation. -/
noncomputable def productiveGroundValuation
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) : GroundAtom → Prop
  | .con concept term =>
      productiveConceptHolds context extension concept
        (quotientTerm context extension
          (quotientNormalizedTerm context extension term))
  | .rol role source target =>
      productiveRoleHolds context extension role
        (quotientTerm context extension
          (quotientNormalizedTerm context extension source))
        (quotientTerm context extension
          (quotientNormalizedTerm context extension target))
  | .eqa left right =>
      ProductiveCongruence context extension
        (quotientNormalizedTerm context extension left)
        (quotientNormalizedTerm context extension right)

theorem productiveGroundValuation_respectsEq
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) :
    RespectsEq (productiveGroundValuation context extension) := by
  constructor
  · intro term
    exact ProductiveCongruence.refl _
  · intro left right hequal
    exact ProductiveCongruence.symm hequal
  · intro left middle right hleft hright
    exact ProductiveCongruence.trans hleft hright
  · intro concept left right hequal hconcept
    change ProductiveCongruence context extension
      (quotientNormalizedTerm context extension left)
      (quotientNormalizedTerm context extension right) at hequal
    have hquot : quotientTerm context extension
        (quotientNormalizedTerm context extension left) =
        quotientTerm context extension
          (quotientNormalizedTerm context extension right) :=
      Quotient.sound hequal
    change productiveConceptHolds context extension concept
      (quotientTerm context extension
        (quotientNormalizedTerm context extension right))
    change productiveConceptHolds context extension concept
      (quotientTerm context extension
        (quotientNormalizedTerm context extension left)) at hconcept
    rw [hquot] at hconcept
    exact hconcept
  · intro role left right target hequal hrole
    change ProductiveCongruence context extension
      (quotientNormalizedTerm context extension left)
      (quotientNormalizedTerm context extension right) at hequal
    have hquot : quotientTerm context extension
        (quotientNormalizedTerm context extension left) =
        quotientTerm context extension
          (quotientNormalizedTerm context extension right) :=
      Quotient.sound hequal
    change productiveRoleHolds context extension role
      (quotientTerm context extension
        (quotientNormalizedTerm context extension right))
      (quotientTerm context extension
        (quotientNormalizedTerm context extension target))
    change productiveRoleHolds context extension role
      (quotientTerm context extension
        (quotientNormalizedTerm context extension left))
      (quotientTerm context extension
        (quotientNormalizedTerm context extension target)) at hrole
    rw [hquot] at hrole
    exact hrole
  · intro role source left right hequal hrole
    change ProductiveCongruence context extension
      (quotientNormalizedTerm context extension left)
      (quotientNormalizedTerm context extension right) at hequal
    have hquot : quotientTerm context extension
        (quotientNormalizedTerm context extension left) =
        quotientTerm context extension
          (quotientNormalizedTerm context extension right) :=
      Quotient.sound hequal
    change productiveRoleHolds context extension role
      (quotientTerm context extension
        (quotientNormalizedTerm context extension source))
      (quotientTerm context extension
        (quotientNormalizedTerm context extension right))
    change productiveRoleHolds context extension role
      (quotientTerm context extension
        (quotientNormalizedTerm context extension source))
      (quotientTerm context extension
        (quotientNormalizedTerm context extension left)) at hrole
    rw [hquot] at hrole
    exact hrole

theorem evalGroundLiteral_productiveGroundValuation_iff
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (literal : FLit) :
    evalGroundLiteral (productiveGroundValuation context extension) literal ↔
      (productiveQuotientModel context extension).evalL
        (quotientAssignment context extension) literal := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept concept term =>
          unfold evalGroundLiteral productiveGroundValuation
          rw [TModel.evalL, productiveQuotientModel_evalT]
          rfl
      | role role source target =>
          unfold evalGroundLiteral productiveGroundValuation
          rw [TModel.evalL, productiveQuotientModel_evalT,
            productiveQuotientModel_evalT]
          rfl
  | eq left right =>
      unfold evalGroundLiteral productiveGroundValuation
      exact (productiveQuotientModel_eval_eq context extension left right).symm
  | ineq left right =>
      unfold evalGroundLiteral productiveGroundValuation
      exact (productiveQuotientModel_eval_ineq context extension left right).symm

/-- Every positive atom produced by the ordered candidate valuation remains
true after equality congruence closure. -/
theorem productiveGroundValuation_of_Itrue_positive
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (literal : FLit) (atom : GroundAtom)
    (hatom : positiveAtom? literal = some atom)
    (htrue :
      letI : LinearOrder FLit := linearOrder extension
      letI : WellFoundedLT FLit := wellFoundedLT extension
      OrdRes.Itrue (rawSet context.retained) literal) :
    productiveGroundValuation context extension atom := by
  cases literal with
  | P predicate =>
      cases predicate with
      | concept concept term =>
          simp only [positiveAtom?, Option.some.injEq] at hatom
          subst atom
          change productiveConceptHolds context extension concept
            (quotientTerm context extension term)
          exact ⟨term, rfl, htrue⟩
      | role role source target =>
          simp only [positiveAtom?, Option.some.injEq] at hatom
          subst atom
          change productiveRoleHolds context extension role
            (quotientTerm context extension source)
            (quotientTerm context extension target)
          exact ⟨source, target, rfl, rfl, htrue⟩
  | eq left right =>
      simp only [positiveAtom?, Option.some.injEq] at hatom
      subst atom
      exact ProductiveCongruence.productive (by
        simpa [ProductiveEqualityRewrite] using htrue)
  | ineq left right => simp [positiveAtom?] at hatom

#print axioms retained_literal_mem_ordered
#print axioms source_clause_predicateBody
#print axioms source_instance_predicateBody
#print axioms retained_clause_predicateBody
#print axioms exists_live_context_of_production_context
#print axioms self_mem_termAndSubterms
#print axioms retained_equality_term_mem_ordered
#print axioms retained_equality_strictly_decreases
#print axioms productiveEqualityRewrite_decreases
#print axioms productiveEqualityRewrite_terms_mem_ordered
#print axioms productiveEqualityRewrite_wellFounded
#print axioms productiveClassRewrite_wellFounded
#print axioms productiveClassRewrite_directlyJoinable
#print axioms productiveClassNormalForm_idempotent
#print axioms productiveClassNormalForm_mem_ordered
#print axioms productiveClassNormalForm_equivalent
#print axioms productiveClassNormalForm_eq_of_equivalent
#print axioms productiveEquivalence_eq_or_mem_ordered
#print axioms productiveClassNormalForm_eq_of_equivalent_any
#print axioms normalSourceConceptHolds_mk
#print axioms normalSourceRoleHolds_mk
#print axioms normalSourceLiteralValuation_sat_of_normalizeGeneratedHead_none
#print axioms sourceConceptHolds_iff
#print axioms sourceRoleHolds_iff
#print axioms productiveSourceGroundValuation_respectsEq
#print axioms sourceQuotientTerm_productive_eq
#print axioms quotientTerm_productive_eq
#print axioms productiveQuotientModel_evalT
#print axioms productiveConceptHolds_iff
#print axioms productiveRoleHolds_iff
#print axioms productiveQuotientModel_concept_of_true
#print axioms productiveQuotientModel_role_of_true
#print axioms productiveQuotientModel_eval_eq
#print axioms productiveQuotientModel_equality_of_true
#print axioms productiveQuotientModel_eval_ineq
#print axioms productiveGroundValuation_respectsEq
#print axioms evalGroundLiteral_productiveGroundValuation_iff
#print axioms productiveGroundValuation_of_Itrue_positive

end ContextCalculus.CBSourceEqualityCanonicalModel
