namespace ContextCalculus.FiniteDatatypeCover

universe u v

/-- Membership clauses and an exhaustive cover characterize a finite range. -/
theorem cover_iff {D : Type u} {V : Type v}
    (range : D → Prop) (value : V → D → Prop) (values : List V)
    (inside : ∀ v, v ∈ values → ∀ x, value v x → range x)
    (covered : ∀ x, range x → ∃ v, v ∈ values ∧ value v x) :
    ∀ x, range x ↔ ∃ v, v ∈ values ∧ value v x := by
  intro x
  constructor
  · exact covered x
  · rintro ⟨v, hv, hx⟩
    exact inside v hv x hx

/-- Repeated spellings do not change a cover when their value concepts agree. -/
theorem alias_cover {D : Type u} (a b rest : D → Prop)
    (alias : ∀ x, a x ↔ b x) :
    ∀ x, (a x ∨ rest x) ↔ (b x ∨ rest x) := by
  intro x
  constructor
  · intro h
    cases h with
    | inl ha => exact Or.inl ((alias x).mp ha)
    | inr hr => exact Or.inr hr
  · intro h
    cases h with
    | inl hb => exact Or.inl ((alias x).mpr hb)
    | inr hr => exact Or.inr hr

/-- A one-value range cannot supply two distinct property successors. -/
theorem singleton_cover_excludes_distinct_successors {O : Type u} {D : Type v}
    (role : O → D → Prop) (range value : D → Prop)
    (range_axiom : ∀ a x, role a x → range x)
    (cover : ∀ x, range x → value x)
    (identity : ∀ x y, value x → value y → x = y) (a : O) :
    ¬ ∃ x y, role a x ∧ role a y ∧ x ≠ y := by
  rintro ⟨x, y, hx, hy, hne⟩
  exact hne (identity x y (cover x (range_axiom a x hx))
    (cover y (range_axiom a y hy)))

#print axioms cover_iff
#print axioms alias_cover
#print axioms singleton_cover_excludes_distinct_successors

/-- An asserted value unequal to every member of an exhaustive range cannot
occur in a model of the range axiom. Value equality, not lexical spelling,
is the premise used by the finite data-ABox precheck. -/
theorem asserted_value_outside_cover {O : Type u} {D : Type v}
    (role : O → D → Prop) (range : D → Prop) (values : List D)
    (range_axiom : ∀ a x, role a x → range x)
    (covered : ∀ x, range x → ∃ value, value ∈ values ∧ x = value)
    (a : O) (x : D) (asserted : role a x)
    (outside : ∀ value, value ∈ values → x ≠ value) : False := by
  obtain ⟨value, member, equal⟩ := covered x (range_axiom a x asserted)
  exact outside value member equal

#print axioms asserted_value_outside_cover

end ContextCalculus.FiniteDatatypeCover
