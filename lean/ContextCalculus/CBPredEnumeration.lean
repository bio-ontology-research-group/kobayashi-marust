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

example : cartesianSelections ([[0, 1], [2, 3]] : List (List Nat)) =
    [[0, 2], [0, 3], [1, 2], [1, 3]] := by native_decide

example : providersFor
    ([⟨[], [.P (.concept 0 (.var 0))]⟩,
      ⟨[], [.P (.concept 1 (.var 0))]⟩] : List FCL)
    (.P (.concept 0 (.var 0))) = [⟨0, by decide⟩] := by native_decide

#print axioms mem_cartesianSelections_iff
#print axioms Selects.length_eq
#print axioms mem_providersFor_iff
#print axioms mem_provider_product_iff

end ContextCalculus.CBPredEnumeration
