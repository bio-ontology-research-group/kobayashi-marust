namespace ContextCalculus.DLSafeRuleForest
universe u v w

/-- Body-only variables may be existentially quantified once all head variables
are fixed. This preserves all possible matches, including an empty domain. -/
theorem body_only_elimination {H : Type u} {B : Type v}
    (body : H → B → Prop) (head : H → Prop) :
    (∀ h b, body h b → head h) ↔
    (∀ h, (∃ b, body h b) → head h) := by
  constructor
  · intro rule h witness
    obtain ⟨b, hb⟩ := witness
    exact rule h b hb
  · intro rule h b hb
    exact rule h ⟨b, hb⟩

/-- A private anchor cover has precisely the interpreted original named domain
as its targets. Names need not denote distinct objects. -/
theorem named_cover_exists {D : Type u} {I : Type v}
    (name : I → D) (cover : D → D → Prop) (anchor : D)
    (includes : ∀ i, cover anchor (name i))
    (excludes : ∀ x, cover anchor x → ∃ i, name i = x)
    (concept : D → Prop) :
    (∃ x, cover anchor x ∧ concept x) ↔ ∃ i, concept (name i) := by
  constructor
  · rintro ⟨x, edge, hx⟩
    obtain ⟨i, hi⟩ := excludes x edge
    exact ⟨i, hi.symm ▸ hx⟩
  · rintro ⟨i, hi⟩
    exact ⟨name i, includes i, hi⟩

/-- Separate tree branches may choose independent witnesses only when all
shared variables have already been fixed. -/
theorem independent_branches {A : Type u} {B : Type v}
    (left : A → Prop) (right : B → Prop) :
    (∃ a, left a) ∧ (∃ b, right b) ↔ ∃ a b, left a ∧ right b := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨a, b, ha, hb⟩
  · rintro ⟨a, b, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

#print axioms body_only_elimination
#print axioms named_cover_exists
#print axioms independent_branches
end ContextCalculus.DLSafeRuleForest
