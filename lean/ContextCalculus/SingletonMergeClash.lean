namespace ContextCalculus.SingletonMergeClash
universe u

/-- Forced singleton equality conflicts with an independently required inequality.
All three premises are needed in the conflict returned to backtracking. -/
theorem distinct_conflict {D : Type u} (value : D → Prop)
    (singleton : ∀ x y, value x → value y → x = y)
    (x y : D) (left right distinct : Prop)
    (left_value : left → value x) (right_value : right → value y)
    (inequality : distinct → x ≠ y) : ¬ (left ∧ right ∧ distinct) := by
  rintro ⟨hl, hr, hd⟩
  exact inequality hd (singleton x y (left_value hl) (right_value hr))

/-- Opposing labels must likewise clash before the merge can discard either label. -/
theorem opposite_label_conflict {D : Type u} (value label : D → Prop)
    (singleton : ∀ x y, value x → value y → x = y)
    (x y : D) (vx : value x) (vy : value y)
    (positive : label x) (negative : ¬ label y) : False := by
  exact negative ((singleton x y vx vy) ▸ positive)

/-- SameIndividual is represented by a positive singleton-nominal assertion. -/
theorem same_iff_nominal {D : Type u} (a b : D) : a = b ↔ (fun x => x = b) a := by
  rfl

#print axioms distinct_conflict
#print axioms opposite_label_conflict
#print axioms same_iff_nominal
end ContextCalculus.SingletonMergeClash
