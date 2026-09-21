namespace ContextCalculus.NativeSameIndividualSeeds

/-- Positive nominal membership is equality, with no unique-name assumption.
Installing both seed directions preserves exactly the source equality. -/
theorem same_iff_bidirectional_seeds {O : Type} (a b : O) :
    a = b ↔ (a = b ∧ b = a) := by
  constructor
  · intro h
    exact ⟨h, h.symm⟩
  · exact And.left

/-- Merged owners retain all source assertions, including contradictions. -/
theorem same_owner_clash {O : Type} (a b : O) (p : O → Prop)
    (same : a = b) (positive : p a) (negative : ¬ p b) : False := by
  exact negative (same ▸ positive)

#print axioms same_iff_bidirectional_seeds
#print axioms same_owner_clash
end ContextCalculus.NativeSameIndividualSeeds
