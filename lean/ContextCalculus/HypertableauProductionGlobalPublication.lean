import ContextCalculus.HypertableauProductionDecisionTotal

/-!
# Exact global publication from total production HT search

The current two-level production route decides one exact source-level global
semantics.  This module turns its proof-carrying verdict into the Boolean
published by KM and proves both directions of that answer.
-/

namespace ContextCalculus.Hypertableau

/-- One global Boolean answer tied to its exact semantic proposition. -/
structure ExactBooleanGlobalPublication (semantics : Prop) where
  answer : Bool
  answerExact : answer = true ↔ semantics

def CertifiedHTGlobalVerdict.publish
    (verdict : CertifiedHTGlobalVerdict semantics) :
    ExactBooleanGlobalPublication semantics :=
  match verdict with
  | .sat proof => ⟨true, iff_of_true rfl proof⟩
  | .unsat proof => ⟨false, by simp [proof]⟩

/-- Every current assignment-plus-expansion global route publishes exactly the
source satisfiability proposition in its semantic index. -/
theorem CertifiedHTAssignmentProductionGlobalRoute.publishesExactly
    {semantics : Prop}
    (route : CertifiedHTAssignmentProductionGlobalRoute semantics) :
    Nonempty (ExactBooleanGlobalPublication semantics) := by
  rcases route.decides with ⟨verdict⟩
  exact ⟨verdict.publish⟩

theorem ExactBooleanGlobalPublication.false_iff
    (publication : ExactBooleanGlobalPublication semantics) :
    publication.answer = false ↔ ¬semantics := by
  constructor
  · intro hfalse hsemantics
    have htrue := publication.answerExact.mpr hsemantics
    simp [hfalse] at htrue
  · intro hnot
    cases hanswer : publication.answer with
    | false => rfl
    | true => exact False.elim (hnot (publication.answerExact.mp hanswer))

#print axioms CertifiedHTGlobalVerdict.publish
#print axioms CertifiedHTAssignmentProductionGlobalRoute.publishesExactly
#print axioms ExactBooleanGlobalPublication.false_iff

end ContextCalculus.Hypertableau
