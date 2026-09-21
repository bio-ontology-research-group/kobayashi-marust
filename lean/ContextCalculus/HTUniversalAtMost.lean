import ContextCalculus.HypertableauCardinalityProjection

namespace ContextCalculus.Hypertableau

/-- An unguarded equality-only recognition clause is a universal qualified
at-most restriction. It is not contingent on an auxiliary domain trigger. -/
theorem universal_pigeonhole_iff_atMost
    {Domain : Type u} (edge : Domain → Domain → Prop)
    (qualifier : Domain → Prop) (bound : Nat) :
    (∀ source (values : Fin (bound + 1) → Domain),
      (∀ i, edge source (values i) ∧ qualifier (values i)) →
      ∃ i j, i < j ∧ values i = values j) ↔
    (∀ source, HasAtMost bound (fun value => edge source value ∧ qualifier value)) := by
  constructor
  · intro h source
    rintro ⟨values, hinjective, hvalues⟩
    exact (not_injective_iff_equal_pair values).mpr (h source values hvalues) hinjective
  · intro h source values hvalues
    apply (not_injective_iff_equal_pair values).mp
    intro hinjective
    exact h source ⟨values, hinjective, hvalues⟩

/-- Incoming edges use the converse relation, with the same exact bound. -/
theorem inverse_universal_pigeonhole_iff_atMost
    {Domain : Type u} (edge : Domain → Domain → Prop)
    (qualifier : Domain → Prop) (bound : Nat) :
    (∀ target (values : Fin (bound + 1) → Domain),
      (∀ i, edge (values i) target ∧ qualifier (values i)) →
      ∃ i j, i < j ∧ values i = values j) ↔
    (∀ target, HasAtMost bound (fun value => edge value target ∧ qualifier value)) :=
  universal_pigeonhole_iff_atMost (fun target source => edge source target) qualifier bound

#print axioms universal_pigeonhole_iff_atMost
#print axioms inverse_universal_pigeonhole_iff_atMost
end ContextCalculus.Hypertableau
