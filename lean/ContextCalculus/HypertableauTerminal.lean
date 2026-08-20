import ContextCalculus.HypertableauTermination

/-!
# Terminal-state totality for guarded hypertableau search

This module names every reason an HT branch is not a terminal open model: a
clash, an existential without a witness, or a guarded clause grounding whose
head is not discharged. If exhaustive finite search finds none of these, the
existing canonical construction is a model of the ontology.
-/

namespace ContextCalculus.Hypertableau

def State.HasClash (state : State Node Concept Role) : Prop :=
  ∃ node concept,
    state.label node (.pos concept) ∧ state.label node (.negated concept)

def State.HasUnwitnessed (state : State Node Concept Role) : Prop :=
  ∃ node role filler,
    state.obligation role filler node ∧
    ∀ witness, ¬(state.edge role node witness ∧ state.label witness filler)

def State.HasUndischarged (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role)) : Prop :=
  ∃ clause ∈ ontology, ∃ assignment,
    (∀ atom ∈ clause.body, state.holdsAtom assignment atom) ∧
    ∀ atom ∈ clause.head, ¬state.holdsAtom assignment atom

theorem State.clashFree_of_noClash
    (state : State Node Concept Role) (hterminal : ¬state.HasClash) :
    state.ClashFree := by
  intro node concept hclash
  exact hterminal ⟨node, concept, hclash⟩

theorem State.witnessComplete_of_noUnwitnessed
    (state : State Node Concept Role) (hterminal : ¬state.HasUnwitnessed) :
    state.WitnessComplete := by
  intro node role filler hobligation
  by_contra hnowitness
  exact hterminal ⟨node, role, filler, hobligation,
    fun witness hwitness => hnowitness ⟨witness, hwitness⟩⟩

theorem State.saturatedFor_of_noUndischarged
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hterminal : ¬state.HasUndischarged ontology) :
    state.SaturatedFor ontology := by
  intro clause hclause assignment hbody
  by_contra hnohead
  exact hterminal ⟨clause, hclause, assignment, hbody,
    fun atom hatom hholds => hnohead ⟨atom, hatom, hholds⟩⟩

/-- An exhaustive terminal branch with no obstruction constructs a model. -/
theorem exhaustive_terminal_models
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody)
    (hclash : ¬state.HasClash)
    (hwitness : ¬state.HasUnwitnessed)
    (hsaturated : ¬state.HasUndischarged ontology) :
    state.canonical.models ontology := by
  exact canonical_models_of_saturated state ontology hguarded
    (state.clashFree_of_noClash hclash)
    (state.witnessComplete_of_noUnwitnessed hwitness)
    (state.saturatedFor_of_noUndischarged ontology hsaturated)

/-- Every branch has an explicit next obstruction or is a canonical open model.
On finite signatures, `finite_branch_progress_traces` makes exhaustive recursion
over the first three alternatives finite. -/
theorem terminal_search_dichotomy
    (state : State Node Concept Role)
    (ontology : List (Clause Variable Concept Role))
    (hguarded : ∀ clause ∈ ontology, clause.GuardedBody) :
    state.HasClash ∨ state.HasUnwitnessed ∨ state.HasUndischarged ontology ∨
      state.canonical.models ontology := by
  classical
  by_cases hclash : state.HasClash
  · exact Or.inl hclash
  by_cases hwitness : state.HasUnwitnessed
  · exact Or.inr (Or.inl hwitness)
  by_cases hsaturated : state.HasUndischarged ontology
  · exact Or.inr (Or.inr (Or.inl hsaturated))
  · exact Or.inr (Or.inr (Or.inr
      (exhaustive_terminal_models state ontology hguarded hclash hwitness hsaturated)))

#print axioms State.clashFree_of_noClash
#print axioms State.witnessComplete_of_noUnwitnessed
#print axioms State.saturatedFor_of_noUndischarged
#print axioms exhaustive_terminal_models
#print axioms terminal_search_dichotomy

end ContextCalculus.Hypertableau
