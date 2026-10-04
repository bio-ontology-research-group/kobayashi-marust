namespace ContextCalculus.DataAssertionNormalization
universe u v

theorem has_value_iff {O : Type u} {D : Type v}
    (role : O → D → Prop) (a : O) (value : D) :
    (∃ d, role a d ∧ d = value) ↔ role a value := by
  constructor
  · rintro ⟨d, h, rfl⟩
    exact h
  · intro h
    exact ⟨value, h, rfl⟩

/-- A fresh class defined by DataHasValue preserves positive assertions. -/
theorem alias_assertion_iff {O : Type u} {D : Type v}
    (role : O → D → Prop) (alias : O → Prop) (value : D)
    (definition : ∀ a, alias a ↔ ∃ d, role a d ∧ d = value) (a : O) :
    alias a ↔ role a value :=
  (definition a).trans (has_value_iff role a value)

/-- Negating the same alias preserves negative data-property assertions. -/
theorem negative_alias_assertion_iff {O : Type u} {D : Type v}
    (role : O → D → Prop) (alias : O → Prop) (value : D)
    (definition : ∀ a, alias a ↔ ∃ d, role a d ∧ d = value) (a : O) :
    (¬ alias a) ↔ ¬ role a value := by
  constructor
  · intro h hv
    exact h ((alias_assertion_iff role alias value definition a).mpr hv)
  · intro h ha
    exact h ((alias_assertion_iff role alias value definition a).mp ha)

/-- Adding a fresh alias definition places no extra condition on old symbols. -/
theorem fresh_definition_extension {O : Type u} {D : Type v}
    (role : O → D → Prop) (value : D) (oldFacts : Prop) :
    (∃ alias : O → Prop,
      (∀ a, alias a ↔ ∃ d, role a d ∧ d = value) ∧ oldFacts) ↔ oldFacts := by
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    exact ⟨fun a => ∃ d, role a d ∧ d = value, fun _ => Iff.rfl, h⟩

#print axioms has_value_iff
#print axioms alias_assertion_iff
#print axioms negative_alias_assertion_iff
#print axioms fresh_definition_extension
end ContextCalculus.DataAssertionNormalization
