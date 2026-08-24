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
open ContextCalculus.CBGroundEqualityBridge
open ContextCalculus.Eqv

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

#print axioms retained_literal_mem_ordered
#print axioms self_mem_termAndSubterms
#print axioms retained_equality_term_mem_ordered
#print axioms retained_equality_strictly_decreases
#print axioms productiveEqualityRewrite_decreases
#print axioms productiveEqualityRewrite_terms_mem_ordered
#print axioms productiveEqualityRewrite_wellFounded
#print axioms quotientTerm_productive_eq
#print axioms productiveQuotientModel_evalT
#print axioms productiveQuotientModel_concept_of_true
#print axioms productiveQuotientModel_role_of_true
#print axioms productiveQuotientModel_eval_eq
#print axioms productiveQuotientModel_equality_of_true
#print axioms productiveQuotientModel_eval_ineq
#print axioms productiveGroundValuation_respectsEq
#print axioms evalGroundLiteral_productiveGroundValuation_iff

end ContextCalculus.CBSourceEqualityCanonicalModel
