import Mathlib

/-!
# Canonical normal forms for terminating directly-joinable rewriting

This file isolates the small Newman-style argument used by the CB equality
canonical model.  The relation is written in Lean's well-founded orientation:
`step smaller larger` means that `larger` rewrites in one step to `smaller`.
-/

namespace ContextCalculus.TermRewriting

variable {Term : Type*} (step : Term → Term → Prop)

/-- Every one-step peak is closed by equality or by one further step between
the two reducts.  KM's ordered Eq rule supplies this stronger local property. -/
def DirectlyJoinable : Prop :=
  ∀ {source left right}, step left source → step right source →
    left = right ∨ step left right ∨ step right left

/-- Pick one reduct recursively, stopping exactly at an irreducible term. -/
noncomputable def normalForm (wf : WellFounded step) : Term → Term :=
  by
    classical
    exact wf.fix fun term recurse =>
      if h : ∃ smaller, step smaller term then
        recurse (Classical.choose h) (Classical.choose_spec h)
      else term

theorem normalForm_eq_of_reducible
    (wf : WellFounded step) {term : Term}
    (hreducible : ∃ smaller, step smaller term) :
    normalForm step wf term =
      normalForm step wf (Classical.choose hreducible) := by
  classical
  rw [normalForm, WellFounded.fix_eq]
  simp [hreducible]

theorem normalForm_eq_self_of_irreducible
    (wf : WellFounded step) {term : Term}
    (hirreducible : ¬ ∃ smaller, step smaller term) :
    normalForm step wf term = term := by
  classical
  rw [normalForm, WellFounded.fix_eq]
  simp [hirreducible]

/-- Directly joinable critical peaks make the recursively selected normal form
independent of every one-step choice. -/
theorem normalForm_eq_of_step
    (wf : WellFounded step) (hjoin : DirectlyJoinable step) :
    ∀ {smaller larger}, step smaller larger →
      normalForm step wf smaller = normalForm step wf larger := by
  classical
  intro smaller larger hstep
  revert smaller
  induction larger using wf.induction with
  | h larger ih =>
      intro smaller hstep
      have hexists : ∃ candidate, step candidate larger := ⟨smaller, hstep⟩
      let chosen := Classical.choose hexists
      have hchosen : step chosen larger := Classical.choose_spec hexists
      rw [normalForm_eq_of_reducible step wf hexists]
      rcases hjoin hstep hchosen with hequal | hleft | hright
      · exact congrArg (normalForm step wf) hequal
      · exact ih chosen hchosen hleft
      · exact (ih smaller hstep hright).symm

theorem normalForm_irreducible
    (wf : WellFounded step) :
    ∀ term, ¬ ∃ smaller, step smaller (normalForm step wf term) := by
  classical
  intro term
  induction term using wf.induction with
  | h term ih =>
      by_cases hexists : ∃ smaller, step smaller term
      · rw [normalForm_eq_of_reducible step wf hexists]
        let chosen := Classical.choose hexists
        have hchosen : step chosen term := Classical.choose_spec hexists
        exact ih chosen hchosen
      · rw [normalForm_eq_self_of_irreducible step wf hexists]
        exact hexists

theorem normalForm_preserves
    (wf : WellFounded step) (property : Term → Prop)
    (hstep : ∀ {smaller larger}, step smaller larger →
      property larger → property smaller) :
    ∀ term, property term → property (normalForm step wf term) := by
  classical
  intro term
  induction term using wf.induction with
  | h term ih =>
      intro hproperty
      by_cases hexists : ∃ smaller, step smaller term
      · rw [normalForm_eq_of_reducible step wf hexists]
        exact ih (Classical.choose hexists) (Classical.choose_spec hexists)
          (hstep (Classical.choose_spec hexists) hproperty)
      · rw [normalForm_eq_self_of_irreducible step wf hexists]
        exact hproperty

/-- Normalization is a finite sequence of forward rewrite steps. -/
theorem reflTransGen_normalForm
    (wf : WellFounded step) :
    ∀ term, Relation.ReflTransGen (Function.swap step) term
      (normalForm step wf term) := by
  classical
  intro term
  induction term using wf.induction with
  | h term ih =>
      by_cases hexists : ∃ smaller, step smaller term
      · rw [normalForm_eq_of_reducible step wf hexists]
        let smaller := Classical.choose hexists
        have hsmaller : step smaller term := Classical.choose_spec hexists
        have hforward : Function.swap step term smaller := hsmaller
        exact (Relation.ReflTransGen.single hforward).trans
          (ih smaller hsmaller)
      · rw [normalForm_eq_self_of_irreducible step wf hexists]

#print axioms normalForm_eq_of_reducible
#print axioms normalForm_eq_self_of_irreducible
#print axioms normalForm_eq_of_step
#print axioms normalForm_irreducible
#print axioms normalForm_preserves
#print axioms reflTransGen_normalForm

end ContextCalculus.TermRewriting
