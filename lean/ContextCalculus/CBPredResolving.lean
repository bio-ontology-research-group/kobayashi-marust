import ContextCalculus.CBPredEnumeration

/-!
# Pred with premises on composite edges (docs/PER-CONTEXT-ORDERING.md §15.2)

`CBPredEnumeration.providerPlan` models the Pred dimension setup of the
certified CB surface: a payload body literal without a provider is copied
verbatim into the conclusion when the transported literal is ground.

Outside the certified surface, KM (v1.5.5, agent `objvalue-cost`) records on an
edge labelled by a composite `f(o)` the transported images of the sender's
atoms over `x` (`PredClause.resolve`). Those are premises `A_iσ` of the
paper's Pred (arXiv:1805.01396 Table 2) and are never copied; they must
resolve against a receiver clause. `providerPlanResolving` is that rule.

`providerPlanResolving_sub`: whenever the restored rule produces a plan, the
certified rule produces the same plan. Every conclusion of the restored rule
is therefore a conclusion of the certified rule (and inherits its soundness,
`CBInterContext.predTransfer_sound`); a recorded premise without a provider
rejects the arrival (`providerPlanResolving_none_of_premise`), and with an
empty `resolve` the two definitions coincide clause by clause.
-/

namespace ContextCalculus.CBPredResolving

open ContextCalculus ContextCalculus.CheckerTerm
open ContextCalculus.CBPredEnumeration

/-- The restored dimension setup: as `providerPlan`, except that a literal of
`resolve` without a provider rejects the arrival instead of being copied. -/
def providerPlanResolving (retained : List FCL) (resolve : List FLit) : List FLit →
    Option (List (ProviderDimension retained) × List FLit)
  | [] => some ([], [])
  | literal :: body =>
      let providers := providersFor retained literal
      if providers.isEmpty then
        if groundLiteral literal && !(resolve.contains literal) then
          match providerPlanResolving retained resolve body with
          | some (dimensions, remainder) =>
              some (dimensions, literal :: remainder)
          | none => none
        else none
      else
        match providerPlanResolving retained resolve body with
        | some (dimensions, remainder) =>
            some ((literal, providers) :: dimensions, remainder)
        | none => none

/-- **The restored rule refines the certified rule.** -/
theorem providerPlanResolving_sub (retained : List FCL) (resolve : List FLit) :
    ∀ {body : List FLit} {plan : List (ProviderDimension retained) × List FLit},
      providerPlanResolving retained resolve body = some plan →
      providerPlan retained body = some plan := by
  intro body
  induction body with
  | nil =>
      intro plan h
      simpa [providerPlanResolving, providerPlan] using h
  | cons literal body ih =>
      intro plan h
      by_cases hempty : (providersFor retained literal).isEmpty = true
      · by_cases hcopy : (groundLiteral literal && !(resolve.contains literal)) = true
        · have hground : groundLiteral literal = true := by
            simp only [Bool.and_eq_true] at hcopy; exact hcopy.1
          simp only [providerPlanResolving, hempty, hcopy, if_true] at h
          cases htail : providerPlanResolving retained resolve body with
          | none => simp [htail] at h
          | some tail =>
              simp only [htail] at h
              simp [providerPlan, hempty, hground, ih htail, h]
        · simp [providerPlanResolving, hempty] at h
          exfalso
          apply hcopy
          simp [h.1.1, h.1.2]
      · have hne : (providersFor retained literal).isEmpty = false :=
          Bool.eq_false_of_not_eq_true hempty
        simp only [providerPlanResolving, hne, Bool.false_eq_true, if_false] at h
        cases htail : providerPlanResolving retained resolve body with
        | none => simp [htail] at h
        | some tail =>
            simp only [htail] at h
            simp [providerPlan, hne, ih htail, h]

/-- A recorded premise without a provider rejects the arrival. -/
theorem providerPlanResolving_none_of_premise (retained : List FCL) (resolve : List FLit)
    (literal : FLit) (body : List FLit)
    (hempty : providersFor retained literal = []) (hmem : literal ∈ resolve) :
    providerPlanResolving retained resolve (literal :: body) = none := by
  simp only [providerPlanResolving, hempty, List.isEmpty_nil, if_true]
  simp
  intro _ hn
  exact absurd hmem hn

#print axioms providerPlanResolving_sub
#print axioms providerPlanResolving_none_of_premise

end ContextCalculus.CBPredResolving
