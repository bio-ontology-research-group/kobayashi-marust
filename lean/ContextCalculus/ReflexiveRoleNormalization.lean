namespace ContextCalculus.ReflexiveRoleNormalization

universe u

/-- Universal reflexivity and a global SELF restriction have the same models. -/
theorem reflexive_iff_global_self {D : Type u} (R : D → D → Prop) :
    (∀ x, R x x) ↔ (∀ x, True → R x x) := by
  constructor
  · intro h x _
    exact h x
  · intro h x
    exact h x True.intro

/-- Reflexivity makes a universal restriction apply at its own subject. -/
theorem universal_at_subject {D : Type u} (R : D → D → Prop)
    (C : D → Prop) (refl : ∀ x, R x x) (x : D)
    (all : ∀ y, R x y → C y) : C x :=
  all x (refl x)

/-- The global restriction also applies to existential witnesses. -/
theorem no_successor_of_self_contradictory_class {D : Type u}
    (R S : D → D → Prop) (A : D → Prop)
    (refl : ∀ x, R x x)
    (disjoint : ∀ x, A x → ∀ y, R x y → ¬ A y) (x : D) :
    ¬ ∃ y, S x y ∧ A y := by
  rintro ⟨y, _, ay⟩
  exact disjoint y ay y (refl y) ay

#print axioms reflexive_iff_global_self
#print axioms universal_at_subject
#print axioms no_successor_of_self_contradictory_class
end ContextCalculus.ReflexiveRoleNormalization
