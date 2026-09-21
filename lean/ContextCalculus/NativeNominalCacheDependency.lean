namespace ContextCalculus.NativeNominalCacheDependency

/-- A value restriction reaches the actual named object and therefore its
asserted type. An unrelated cardinality axiom cannot remove this consequence.
The premise uses ordinary relational semantics, with no unique-name axiom. -/
theorem named_successor_entailment {O : Type}
    (a : O) (source target part past : O → Prop) (role : O → O → Prop)
    (valueRestriction : ∀ x, source x → role x a ∧ part x)
    (asserted : past a)
    (definition : ∀ x, target x ↔ part x ∧ ∃ y, role x y ∧ past y) :
    ∀ x, source x → target x := by
  intro x hx
  obtain ⟨edge, member⟩ := valueRestriction x hx
  exact (definition x).mpr ⟨member, a, edge, asserted⟩

/-- A purported countermodel missing this target is invalid even if its
nominal-free cached label is locally closed. The actual named assertion is
part of the source model obligations. -/
theorem no_countermodel_without_named_assertion {O : Type}
    (a x : O) (source target part past : O → Prop) (role : O → O → Prop)
    (valueRestriction : ∀ y, source y → role y a ∧ part y)
    (asserted : past a)
    (definition : ∀ y, target y ↔ part y ∧ ∃ z, role y z ∧ past z)
    (positive : source x) (negative : ¬target x) : False :=
  negative (named_successor_entailment a source target part past role
    valueRestriction asserted definition x positive)

#print axioms named_successor_entailment
#print axioms no_countermodel_without_named_assertion
end ContextCalculus.NativeNominalCacheDependency
