import ContextCalculus.CBSourceHyperClosure

/-!
# Computed finite linear extensions of the source-bound literal order

The canonical model needs a total well-founded rank, while production fires on
all maxima of its partial literal order. This module computes a deterministic
topological order over the exact finite source/live support and verifies the
result before exposing its rank.
-/

namespace ContextCalculus.CBSourceLinearExtension

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBSourceHyperClosure

def noIncoming (order : DecodedSourceFiniteOrder production) (root : Bool)
    (remaining : List FLit) (candidate : FLit) : Bool :=
  remaining.all fun other =>
    decide (other = candidate) || !order.literalLe root other candidate

def topologicalOrderAux (order : DecodedSourceFiniteOrder production)
    (root : Bool) : Nat → List FLit → List FLit
  | 0, _ => []
  | fuel + 1, remaining =>
      match remaining.find? (noIncoming order root remaining) with
      | none => []
      | some next => next :: topologicalOrderAux order root fuel
          (without next remaining)

def topologicalOrder (order : DecodedSourceFiniteOrder production)
    (root : Bool) : List FLit :=
  topologicalOrderAux order root order.orderedLiterals.length
    order.orderedLiterals

structure ComputedLinearExtension
    (order : DecodedSourceFiniteOrder production) (root : Bool) where
  linear : List FLit
  nodup : linear.Nodup
  support_exact : linear.toFinset = order.orderedLiterals.toFinset
  preserves : ∀ left ∈ order.orderedLiterals,
    ∀ right ∈ order.orderedLiterals,
      order.literalLe root left right = true → left ≠ right →
        linear.idxOf left < linear.idxOf right

def computeLinearExtension
    (order : DecodedSourceFiniteOrder production) (root : Bool) :
    Except String (ComputedLinearExtension order root) :=
  let linear := topologicalOrder order root
  if hnodup : linear.Nodup then
    if hexact : linear.toFinset = order.orderedLiterals.toFinset then
      if hpreserves : ∀ left ∈ order.orderedLiterals,
          ∀ right ∈ order.orderedLiterals,
            order.literalLe root left right = true → left ≠ right →
              linear.idxOf left < linear.idxOf right then
        .ok (ComputedLinearExtension.mk linear hnodup hexact hpreserves)
      else .error "computed literal order does not extend production order"
    else .error "computed literal order does not cover production support"
  else .error "computed literal order contains a duplicate"

def ComputedLinearExtension.rank
    (extension : ComputedLinearExtension order root) (literal : FLit) : Nat :=
  extension.linear.idxOf literal

theorem ComputedLinearExtension.mem_linear_iff
    (extension : ComputedLinearExtension order root) (literal : FLit) :
    literal ∈ extension.linear ↔ literal ∈ order.orderedLiterals := by
  simpa only [List.mem_toFinset] using
    Finset.ext_iff.mp extension.support_exact literal

theorem ComputedLinearExtension.linearExtensionOn
    (extension : ComputedLinearExtension order root) :
    LinearExtensionOn order root order.orderedLiterals extension.rank := by
  constructor
  · intro left hleft right _ hrank
    exact (List.idxOf_inj
      ((extension.mem_linear_iff left).mpr hleft)).mp hrank
  · intro left hleft right hright hle
    by_cases hequal : left = right
    · subst right
      exact Nat.le_refl _
    · exact Nat.le_of_lt
        (extension.preserves left hleft right hright hle hequal)

theorem ComputedLinearExtension.headLinearExtensionOn
    (extension : ComputedLinearExtension order root)
    (head : List FLit)
    (hsupport : ∀ literal ∈ head, literal ∈ order.orderedLiterals) :
    LinearExtensionOn order root head extension.rank := by
  constructor
  · intro left hleft right _ hrank
    exact (List.idxOf_inj
      ((extension.mem_linear_iff left).mpr (hsupport left hleft))).mp hrank
  · intro left hleft right hright hle
    exact extension.linearExtensionOn.preserves left (hsupport left hleft)
      right (hsupport right hright) hle

#print axioms ComputedLinearExtension.linearExtensionOn
#print axioms ComputedLinearExtension.headLinearExtensionOn

end ContextCalculus.CBSourceLinearExtension
