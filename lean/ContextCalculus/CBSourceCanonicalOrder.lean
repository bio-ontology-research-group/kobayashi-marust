import ContextCalculus.CBSourceCanonicalClosure
import Mathlib.Tactic.DeriveEncodable
import Mathlib

/-!
# Global well-founded literal order from a checked source extension

The source certificate ranks exactly the finite literals relevant to one KM
run. Ordered resolution nevertheless expects a global order on `FLit`. We put
the checked support first in its verified rank order and place every remaining
literal afterwards by its injective structural encoding. The resulting global
order is linear and well-founded and agrees with the checked rank on support.
-/

namespace ContextCalculus.CBSourceCanonicalOrder

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBSourceHyperClosure
open ContextCalculus.CBSourceLinearExtension
open ContextCalculus.CBFiniteLiteralOrderWire
open ContextCalculus.CBProductionTraceWire

deriving instance Encodable for FTerm
deriving instance Encodable for FPred
deriving instance Encodable for FLit

def orderingKey (extension : ComputedLinearExtension order root)
    (literal : FLit) : Nat :=
  if literal ∈ extension.linear then
    2 * extension.rank literal
  else
    2 * Encodable.encode literal + 1

theorem orderingKey_injective
    (extension : ComputedLinearExtension order root) :
    Function.Injective (orderingKey extension) := by
  intro left right hequal
  by_cases hleft : left ∈ extension.linear
  · by_cases hright : right ∈ extension.linear
    · have hrank : extension.rank left = extension.rank right := by
        simp only [orderingKey, if_pos hleft, if_pos hright] at hequal
        exact Nat.mul_left_cancel (by omega) hequal
      exact (List.idxOf_inj hleft).mp hrank
    · simp [orderingKey, hleft, hright] at hequal
      omega
  · by_cases hright : right ∈ extension.linear
    · simp [orderingKey, hleft, hright] at hequal
      omega
    · have hencode : Encodable.encode left = Encodable.encode right := by
        simp only [orderingKey, if_neg hleft, if_neg hright] at hequal
        exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel hequal)
      exact Encodable.encode_injective hencode

@[reducible] def linearOrder (extension : ComputedLinearExtension order root) :
    LinearOrder FLit :=
  LinearOrder.lift' (orderingKey extension) (orderingKey_injective extension)

@[reducible] def wellFoundedLT (extension : ComputedLinearExtension order root) :
    @WellFoundedLT FLit (linearOrder extension).toLT :=
  ⟨by
    simpa [linearOrder] using
      (WellFounded.onFun (f := orderingKey extension) wellFounded_lt)⟩

theorem le_iff_key_le
    (extension : ComputedLinearExtension order root)
    (left right : FLit) :
    @LE.le FLit (linearOrder extension).toLE left right ↔
      orderingKey extension left ≤ orderingKey extension right :=
  Iff.rfl

theorem supported_rank_le_iff
    (extension : ComputedLinearExtension order root)
    {left right : FLit}
    (hleft : left ∈ extension.linear) (hright : right ∈ extension.linear) :
    @LE.le FLit (linearOrder extension).toLE left right ↔
      extension.rank left ≤ extension.rank right := by
  simp [le_iff_key_le, orderingKey, hleft, hright]

theorem production_le_implies_global_le
    (extension : ComputedLinearExtension order root)
    {left right : FLit}
    (hleft : left ∈ order.orderedLiterals)
    (hright : right ∈ order.orderedLiterals)
    (hle : order.literalLe root left right = true) :
    @LE.le FLit (linearOrder extension).toLE left right := by
  rw [supported_rank_le_iff extension
    ((extension.mem_linear_iff left).mpr hleft)
    ((extension.mem_linear_iff right).mpr hright)]
  exact extension.linearExtensionOn.preserves left hleft right hright hle

theorem retained_literal_mem_ordered
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology)
    (hcontext : context ∈ production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    (literal : FLit) (hliteral : literal ∈ clauseLiterals clause) :
    literal ∈ order.orderedLiterals := by
  rw [← List.mem_toFinset, order.literals_exact, List.mem_toFinset]
  simp only [sourceProductionLiterals, List.mem_eraseDups, List.mem_append,
    List.mem_flatMap]
  exact Or.inr ⟨context, hcontext, clause, hclause, hliteral⟩

theorem retained_head_mem_ordered
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology)
    (hcontext : context ∈ production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    (literal : FLit) (hliteral : literal ∈ clause.head) :
    literal ∈ order.orderedLiterals :=
  retained_literal_mem_ordered order context hcontext clause hclause literal
    (by simp [clauseLiterals, hliteral])

/-- A head maximum selected by the checked canonical rank is one of the exact
partial-order maxima for which production Hyper/Eq coverage was checked. -/
theorem canonical_max_is_production_maximal
    (order : DecodedSourceFiniteOrder production)
    (context : DecodedProductionContext production.bounds
      production.source.ontology)
    (hcontext : context ∈ production.contexts)
    (clause : FCL) (hclause : clause ∈ context.retained)
    (extension : ComputedLinearExtension order context.root)
    (index : Nat) (literal : FLit)
    (hindex : clause.head[index]? = some literal)
    (hmax : ∀ other ∈ clause.head,
      extension.rank other ≤ extension.rank literal) :
    index ∈ order.maximalHeadIndices context.root clause.head := by
  apply total_rank_maximal_is_production_maximal order context.root clause.head
    extension.rank
    (extension.headLinearExtensionOn clause.head
      (fun candidate hcandidate =>
        retained_head_mem_ordered order context hcontext clause hclause
          candidate hcandidate)) index literal hindex hmax

#print axioms orderingKey_injective
#print axioms production_le_implies_global_le
#print axioms retained_literal_mem_ordered
#print axioms canonical_max_is_production_maximal

end ContextCalculus.CBSourceCanonicalOrder
