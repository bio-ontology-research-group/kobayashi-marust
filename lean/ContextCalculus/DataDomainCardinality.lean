namespace ContextCalculus.DataDomainCardinality
universe u v

/-- A data-property domain requiring zero values forces that property empty. -/
theorem zero_domain_iff_empty {O : Type u} {D : Type v} (role : O → D → Prop) :
    (∀ a, (∃ d, role a d) → ¬ ∃ d, role a d) ↔ ∀ a d, ¬ role a d := by
  constructor
  · intro domain a d edge
    exact domain a ⟨d, edge⟩ ⟨d, edge⟩
  · intro empty a witness
    rcases witness with ⟨d, edge⟩
    exact False.elim (empty a d edge)

/-- Any class requiring a value of such a property is unsatisfiable. -/
theorem existential_class_empty {O : Type u} {D : Type v}
    (role : O → D → Prop) (cls : O → Prop)
    (domain : ∀ a, (∃ d, role a d) → ¬ ∃ d, role a d)
    (requires : ∀ a, cls a → ∃ d, role a d) : ∀ a, ¬ cls a := by
  intro a member
  exact domain a (requires a member) (requires a member)

#print axioms zero_domain_iff_empty
#print axioms existential_class_empty
end ContextCalculus.DataDomainCardinality
