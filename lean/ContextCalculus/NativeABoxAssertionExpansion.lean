import ContextCalculus.HypertableauNativeABoxProjection

namespace ContextCalculus.Hypertableau
variable {Individual Concept Role Domain : Type}

/-- Raw asserted conjunctions retain their operand obligations independently
of whether an earlier saturation task produced a reusable cache entry. -/
theorem NativeABox.models.asserted_conjunct
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain)
    (model : abox.models I value) (owner : Individual) (conjunction : Concept)
    (operands : List Concept) (asserted : conjunction ∈ abox.assertions owner)
    (meaning : ∀ x, I.concept conjunction x ↔ ∀ c ∈ operands, I.concept c x)
    (operand : Concept) (member : operand ∈ operands) :
    I.concept operand (value owner) :=
  (meaning (value owner)).mp (model.2.1 owner conjunction asserted) operand member

/-- Scheduling consequences already entailed by raw assertions preserves
exactly the source ABox models; absence of a cache is not an omission premise. -/
theorem NativeABox.models.append_asserted_consequences_iff
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain)
    (extra : Individual → List Concept)
    (entailed : ∀ i c, c ∈ extra i → ∃ a, a ∈ abox.assertions i ∧
      ∀ x, I.concept a x → I.concept c x) :
    ({ abox with assertions := fun i => abox.assertions i ++ extra i }).models I value ↔
      abox.models I value := by
  constructor
  · intro h
    refine ⟨h.1, ?_, h.2.2⟩
    intro i c hc
    exact h.2.1 i c (List.mem_append_left _ hc)
  · intro h
    refine ⟨h.1, ?_, h.2.2⟩
    intro i c hc
    rcases List.mem_append.mp hc with original | added
    · exact h.2.1 i c original
    · obtain ⟨a, ha, consequence⟩ := entailed i c added
      exact consequence (value i) (h.2.1 i a ha)

#print axioms NativeABox.models.asserted_conjunct
#print axioms NativeABox.models.append_asserted_consequences_iff
end ContextCalculus.Hypertableau
