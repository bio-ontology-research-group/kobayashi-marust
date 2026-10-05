import ContextCalculus.EndpointRoleHierarchy
/-! The existing three-clause transitivity recognition is a conservative
replacement for guarded source-endpoint class consumers. -/
namespace ContextCalculus.EndpointTransitivity
variable {D : Type}

theorem recognition_reaches {R : D → D → Prop} {C P : D → Prop}
    (seed : ∀ a b, R a b → C b → P a)
    (propagate : ∀ a b, R a b → P b → P a)
    {a b : D} (path : Reach R a b) (target : C b) : P a := by
  induction path with
  | edge edge => exact seed _ _ edge target
  | step edge _ ih => exact propagate _ _ edge (ih target)

theorem guarded_consumer_preserved {R : D → D → Prop} {C G H P : D → Prop}
    (seed : ∀ a b, R a b → C b → P a)
    (propagate : ∀ a b, R a b → P b → P a)
    (publish : ∀ a, G a → P a → H a) :
    ∀ a b, Reach R a b → G a → C b → H a := by
  intro a b path guard target
  exact publish a guard (recognition_reaches seed propagate path target)

theorem recognition_extension {R : D → D → Prop} {C G H : D → Prop}
    (transitive : ∀ a b c, R a b → R b c → R a c)
    (consumer : ∀ a b, R a b → G a → C b → H a) :
    ∃ P : D → Prop,
      (∀ a b, R a b → C b → P a) ∧
      (∀ a b, R a b → P b → P a) ∧
      (∀ a, G a → P a → H a) := by
  refine ⟨fun a => ∃ b, R a b ∧ C b, ?_, ?_, ?_⟩
  · intro a b edge target
    exact ⟨b, edge, target⟩
  · intro a b edge witness
    obtain ⟨c, next, target⟩ := witness
    exact ⟨c, transitive a b c edge next, target⟩
  · intro a guard witness
    obtain ⟨b, edge, target⟩ := witness
    exact consumer a b edge guard target

#print axioms recognition_reaches
#print axioms guarded_consumer_preserved
#print axioms recognition_extension
end ContextCalculus.EndpointTransitivity
