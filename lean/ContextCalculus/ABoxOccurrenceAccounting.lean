/-! Duplicate source occurrences do not create additional constraints.
The source frontend may count accepted duplicates separately from the set-like
rich AST, but may not count an item that parsing failed to represent. -/
namespace ContextCalculus.ABoxOccurrenceAccounting
variable {Axiom : Type}

theorem duplicate_constraint (background fact : Prop) :
    (background ∧ fact ∧ fact) ↔ (background ∧ fact) := by
  constructor
  · rintro ⟨h, hf, _⟩
    exact ⟨h, hf⟩
  · rintro ⟨h, hf⟩
    exact ⟨h, hf, hf⟩

theorem same_members_same_models (before after : List Axiom)
    (holds : Axiom → Prop)
    (represented : ∀ item, item ∈ before ↔ item ∈ after) :
    (∀ item, item ∈ before → holds item) ↔
      (∀ item, item ∈ after → holds item) := by
  constructor
  · intro h item ha
    exact h item ((represented item).mpr ha)
  · intro h item ha
    exact h item ((represented item).mp ha)

#print axioms duplicate_constraint
#print axioms same_members_same_models
end ContextCalculus.ABoxOccurrenceAccounting
