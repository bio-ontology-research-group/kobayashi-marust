import ContextCalculus.HypertableauNativeABoxProjection

namespace ContextCalculus.Hypertableau

/-- Installing a complete typed ABox commutes with retaining every clause of
an independently encoded theory. No nonempty source-TBox premise is needed.
In particular, an empty source side channel cannot justify dropping a clause.
The Rust encoder and its coverage checks remain implementation obligations. -/
theorem nativeABoxSeed_with_retained_theory_iff
    {Individual Concept Role Domain Variable : Type}
    (abox : NativeABox Individual Concept Role)
    (I : Interp Domain Concept Role) (value : Individual → Domain)
    (theory : List (Clause Variable Concept Role)) :
    ((∀ clause ∈ theory, I.modelsClause clause) ∧
      (nativeABoxSeed abox).RealizedBy I value ∧
      abox.ProxySingletons I value ∧ abox.NegativeRoles I value) ↔
    ((∀ clause ∈ theory, I.modelsClause clause) ∧ abox.models I value) := by
  constructor
  · intro h
    exact ⟨h.1, (nativeABoxSeed_realized_iff abox I value).mp h.2⟩
  · intro h
    exact ⟨h.1, (nativeABoxSeed_realized_iff abox I value).mpr h.2⟩

#print axioms nativeABoxSeed_with_retained_theory_iff
end ContextCalculus.Hypertableau
