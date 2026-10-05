/-! Endpoint-only transitivity model extension. The source syntactic guard
remains a normalization boundary, not an extracted Lean implementation. -/
namespace ContextCalculus.EndpointTransitivity
variable {D : Type}
inductive Reach (R : D → D → Prop) : D → D → Prop where
  | edge {a b} : R a b → Reach R a b
  | step {a b c} : R a b → Reach R b c → Reach R a c

theorem reach_transitive {R : D → D → Prop} {a b c : D}
    (left : Reach R a b) (right : Reach R b c) : Reach R a c := by
  induction left with
  | edge h => exact .step h right
  | step h _ ih => exact .step h (ih right)

theorem reach_source {R : D → D → Prop} {a b : D}
    (path : Reach R a b) : ∃ c, R a c := by
  cases path with
  | edge h => exact ⟨_, h⟩
  | step h _ => exact ⟨_, h⟩

theorem reach_target {R : D → D → Prop} {a b : D}
    (path : Reach R a b) : ∃ c, R c b := by
  induction path with
  | edge h => exact ⟨_, h⟩
  | step _ _ ih => exact ih

theorem domain_preserved {R : D → D → Prop} {P : D → Prop}
    (domain : ∀ a b, R a b → P a) : ∀ a b, Reach R a b → P a := by
  intro a b path
  obtain ⟨c, edge⟩ := reach_source path
  exact domain a c edge

theorem range_preserved {R : D → D → Prop} {P : D → Prop}
    (range : ∀ a b, R a b → P b) : ∀ a b, Reach R a b → P b := by
  intro a b path
  obtain ⟨c, edge⟩ := reach_target path
  exact range c b edge

/-- All concept and individual interpretations stay fixed: only R is closed. -/
theorem transitive_model_extension (Theory : (D → D → Prop) → Prop)
    (R : D → D → Prop)
    (extend : ∀ S, (∀ a b, R a b → S a b) →
      (∀ a b, S a b → ∃ c, R a c) →
      (∀ a b, S a b → ∃ c, R c b) → Theory S) :
    ∃ S, Theory S ∧ (∀ a b c, S a b → S b c → S a c) := by
  exact ⟨Reach R, extend _ (fun _ _ h => .edge h)
    (fun _ _ h => reach_source h) (fun _ _ h => reach_target h),
    fun _ _ _ h k => reach_transitive h k⟩

#print axioms reach_transitive
#print axioms domain_preserved
#print axioms range_preserved
#print axioms transitive_model_extension
end ContextCalculus.EndpointTransitivity
