import ContextCalculus.CBSourceGroundResolutionBridge

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

/-- Congruence generated by productive equalities.  The application
constructor is essential: quotienting terms must interpret every unary Skolem
function independently of representatives. -/
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
  | refl (term) : ProductiveCongruence context extension term term
  | symm {left right} : ProductiveCongruence context extension left right →
      ProductiveCongruence context extension right left
  | trans {left middle right} :
      ProductiveCongruence context extension left middle →
      ProductiveCongruence context extension middle right →
      ProductiveCongruence context extension left right
  | app (function : Nat) {left right} :
      ProductiveCongruence context extension left right →
      ProductiveCongruence context extension (.app function left)
        (.app function right)

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

def quotientApp
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root) (function : Nat) :
    ProductiveQuotient context extension → ProductiveQuotient context extension :=
  Quotient.map (.app function) (fun _ _ hequal =>
    ProductiveCongruence.app function hequal)

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

@[simp] theorem quotientApp_quotientTerm
    {decoded : DecodedSourceRootPredClosureDocument}
    (context : DecodedProductionContext
      (liveOf decoded).production.bounds
      (liveOf decoded).production.source.ontology)
    (extension : ComputedLinearExtension
      (hyperOf decoded).order context.root)
    (function : Nat) (term : FTerm) :
    quotientApp context extension function (quotientTerm context extension term) =
      quotientTerm context extension (.app function term) := rfl

#print axioms retained_literal_mem_ordered
#print axioms self_mem_termAndSubterms
#print axioms retained_equality_term_mem_ordered
#print axioms retained_equality_strictly_decreases
#print axioms productiveEqualityRewrite_decreases
#print axioms productiveEqualityRewrite_wellFounded
#print axioms quotientTerm_productive_eq
#print axioms quotientApp_quotientTerm

end ContextCalculus.CBSourceEqualityCanonicalModel
