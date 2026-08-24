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

#print axioms retained_literal_mem_ordered
#print axioms self_mem_termAndSubterms
#print axioms retained_equality_term_mem_ordered
#print axioms retained_equality_strictly_decreases

end ContextCalculus.CBSourceEqualityCanonicalModel
