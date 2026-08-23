import ContextCalculus.CBInterContextWire

/-!
# Exact finite provider enumeration for production CB Pred

Production `pred_from_neighbor` builds one provider dimension for each payload
body literal that can be discharged in the receiver and enumerates their
Cartesian product. This module defines that finite product independently of
enumeration order and proves its membership exact.
-/

namespace ContextCalculus.CBPredEnumeration

open ContextCalculus ContextCalculus.CheckerTerm

/-- One choice from every finite dimension, preserving dimension order. -/
def Selects {α : Type} : List α → List (List α) → Prop
  | [], [] => True
  | choice :: choices, dimension :: dimensions =>
      choice ∈ dimension ∧ Selects choices dimensions
  | _, _ => False

/-- Executable Cartesian product used by the Pred coverage checker. -/
def cartesianSelections {α : Type} : List (List α) → List (List α)
  | [] => [[]]
  | dimension :: dimensions =>
      dimension.flatMap fun choice =>
        (cartesianSelections dimensions).map fun choices => choice :: choices

theorem mem_cartesianSelections_iff {α : Type} [DecidableEq α]
    (choices : List α) (dimensions : List (List α)) :
    choices ∈ cartesianSelections dimensions ↔ Selects choices dimensions := by
  induction dimensions generalizing choices with
  | nil =>
      cases choices <;> simp [cartesianSelections, Selects]
  | cons dimension dimensions ih =>
      cases choices with
      | nil => simp [cartesianSelections, Selects]
      | cons choice choices =>
          simp only [cartesianSelections, List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨selected, hselected, tail, htail, heq⟩
            cases heq
            exact ⟨hselected, (ih choices).mp htail⟩
          · rintro ⟨hchoice, htail⟩
            exact ⟨choice, hchoice, choices,
              (ih choices).mpr htail, rfl⟩

/-- Every generated selection has exactly one entry per dimension. -/
theorem Selects.length_eq {α : Type} {choices : List α}
    {dimensions : List (List α)} (hselects : Selects choices dimensions) :
    choices.length = dimensions.length := by
  induction choices generalizing dimensions with
  | nil => cases dimensions <;> simp_all [Selects]
  | cons choice choices ih =>
      cases dimensions with
      | nil => simp [Selects] at hselects
      | cons dimension dimensions =>
          simp only [Selects] at hselects
          simp [ih hselects.2]

/-- The complete receiver-retained provider index for one payload body
literal. No serialized posting list is trusted: the checker computes it from
the accepted retained snapshot. -/
def providersFor (retained : List FCL) (literal : FLit) :
    List (Fin retained.length) :=
  (List.finRange retained.length).filter fun index =>
    decide (literal ∈ (retained.get index).head)

theorem mem_providersFor_iff (retained : List FCL) (literal : FLit)
    (index : Fin retained.length) :
    index ∈ providersFor retained literal ↔
      literal ∈ (retained.get index).head := by
  simp [providersFor]

/-- A Cartesian provider selection computed from the complete retained
posting lists is extensionally exact. -/
theorem mem_provider_product_iff
    (retained : List FCL) (literals : List FLit)
    (selection : List (Fin retained.length)) :
    selection ∈ cartesianSelections (literals.map (providersFor retained)) ↔
      Selects selection (literals.map (providersFor retained)) :=
  mem_cartesianSelections_iff selection _

/-! ## Production ground-remainder planning -/

/-- Production groundness for the nested-term certificate language. A ground
term contains no universally assigned variable; constants and nested function
applications over ground arguments are ground. -/
def groundTerm : FTerm → Bool
  | .var _ => false
  | .const _ => true
  | .app _ argument => groundTerm argument

def groundPredicate : FPred → Bool
  | .concept _ term => groundTerm term
  | .role _ source target => groundTerm source && groundTerm target

def groundLiteral : FLit → Bool
  | .P predicate => groundPredicate predicate
  | .eq left right | .ineq left right => groundTerm left && groundTerm right

abbrev ProviderDimension (retained : List FCL) :=
  FLit × List (Fin retained.length)

/-- Exact recursive specification of `pred_from_neighbor`'s dimension setup.
Every payload body literal either has its complete nonempty provider posting,
or has no provider and is retained verbatim only when ground. -/
inductive PlanExact (retained : List FCL) :
    List FLit → List (ProviderDimension retained) → List FLit → Prop
  | nil : PlanExact retained [] [] []
  | dimension {literal body dimensions remainder}
      (nonempty : providersFor retained literal ≠ [])
      (rest : PlanExact retained body dimensions remainder) :
      PlanExact retained (literal :: body)
        ((literal, providersFor retained literal) :: dimensions) remainder
  | groundRemainder {literal body dimensions remainder}
      (empty : providersFor retained literal = [])
      (ground : groundLiteral literal = true)
      (rest : PlanExact retained body dimensions remainder) :
      PlanExact retained (literal :: body) dimensions (literal :: remainder)

/-- Build all provider dimensions and the verbatim ground remainder, rejecting
the entire arrival when a non-ground body literal has no provider. -/
def providerPlan (retained : List FCL) : List FLit →
    Option (List (ProviderDimension retained) × List FLit)
  | [] => some ([], [])
  | literal :: body =>
      let providers := providersFor retained literal
      if providers.isEmpty then
        if groundLiteral literal then
          match providerPlan retained body with
          | some (dimensions, remainder) =>
              some (dimensions, literal :: remainder)
          | none => none
        else none
      else
        match providerPlan retained body with
        | some (dimensions, remainder) =>
            some ((literal, providers) :: dimensions, remainder)
        | none => none

theorem providerPlan_exact (retained : List FCL) :
    ∀ {body dimensions remainder},
      providerPlan retained body = some (dimensions, remainder) →
      PlanExact retained body dimensions remainder := by
  intro body
  induction body with
  | nil =>
      intro dimensions remainder hplan
      simp only [providerPlan, Option.some.injEq, Prod.mk.injEq] at hplan
      rcases hplan with ⟨rfl, rfl⟩
      exact .nil
  | cons literal body ih =>
      intro dimensions remainder hplan
      by_cases hempty : providersFor retained literal = []
      · have hisEmpty : (providersFor retained literal).isEmpty = true := by
          simp [hempty]
        by_cases hground : groundLiteral literal = true
        · simp only [providerPlan, hisEmpty, if_pos, hground] at hplan
          cases htail : providerPlan retained body with
          | none => simp [htail] at hplan
          | some tail =>
              rcases tail with ⟨tailDimensions, tailRemainder⟩
              simp only [htail, Option.some.injEq, Prod.mk.injEq] at hplan
              rcases hplan with ⟨rfl, rfl⟩
              exact .groundRemainder hempty hground (ih htail)
        · have hgroundFalse : groundLiteral literal = false :=
            Bool.eq_false_of_not_eq_true hground
          simp [providerPlan, hisEmpty, hgroundFalse] at hplan
      · have hnotEmpty : (providersFor retained literal).isEmpty = false := by
          simpa [List.isEmpty_iff] using hempty
        simp only [providerPlan, hnotEmpty, Bool.false_eq_true, if_false] at hplan
        cases htail : providerPlan retained body with
        | none => simp [htail] at hplan
        | some tail =>
            rcases tail with ⟨tailDimensions, tailRemainder⟩
            simp only [htail, Option.some.injEq, Prod.mk.injEq] at hplan
            rcases hplan with ⟨rfl, rfl⟩
            exact .dimension hempty (ih htail)

example : cartesianSelections ([[0, 1], [2, 3]] : List (List Nat)) =
    [[0, 2], [0, 3], [1, 2], [1, 3]] := by native_decide

example : providersFor
    ([⟨[], [.P (.concept 0 (.var 0))]⟩,
      ⟨[], [.P (.concept 1 (.var 0))]⟩] : List FCL)
    (.P (.concept 0 (.var 0))) = [⟨0, by decide⟩] := by native_decide

example : providerPlan
    ([⟨[], [.P (.concept 0 (.var 0))]⟩] : List FCL)
    [.P (.concept 0 (.var 0)), .P (.concept 1 (.const 0))] =
    some ([⟨.P (.concept 0 (.var 0)), [⟨0, by decide⟩]⟩],
      [.P (.concept 1 (.const 0))]) := by native_decide

example : providerPlan ([] : List FCL)
    [.P (.concept 0 (.var 0))] = none := by native_decide

#print axioms mem_cartesianSelections_iff
#print axioms Selects.length_eq
#print axioms mem_providersFor_iff
#print axioms mem_provider_product_iff
#print axioms providerPlan_exact

end ContextCalculus.CBPredEnumeration
