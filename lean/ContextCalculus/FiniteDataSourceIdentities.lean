import ContextCalculus.FiniteDataMembership

namespace ContextCalculus.FiniteDataMembership

/-- A subproperty edge into the universal data relation places no constraint
on the ordinary relation or the surrounding theory. -/
theorem erase_top_data_inclusion {O D : Type} (theory : Prop) (data : O → D → Prop) :
    (theory ∧ ∀ x v, data x v → (fun (_ : O) (_ : D) => True) x v) ↔ theory := by
  constructor
  · exact And.left
  · intro h
    exact ⟨h, fun _ _ _ => True.intro⟩

/-- Finite data translation preserves the existence of a joint assignment to
anonymous source individuals. Repeated labels use one assignment; distinct
labels need not denote distinct objects. Named individuals keep their fixed
interpretation. Fresh-name allocation and syntactic position checks are
implementation obligations outside this theorem. -/
theorem anonymous_assignment_translation_exact
    {C R P D N A O : Type}
    (classes : C → O → Prop) (roles : R → O → O → Prop) (named : N → O)
    (membership : P → D → O → Prop) (active : D → Prop)
    (assertions : List (Expr C R P D (Sum N A) × Sum N A))
    (admitted : ∀ assertion ∈ assertions, supported active assertion.1) :
    (∃ anonymous : A → O, ∀ assertion ∈ assertions,
      eval classes roles (edge active membership) (Sum.elim named anonymous)
        assertion.1 (Sum.elim named anonymous assertion.2)) ↔
    (∃ anonymous : A → O, ∀ assertion ∈ assertions,
      eval (extendedClasses classes membership) roles (edge active membership)
        (Sum.elim named anonymous) (translate assertion.1)
        (Sum.elim named anonymous assertion.2)) := by
  constructor
  · rintro ⟨anonymous, h⟩
    refine ⟨anonymous, ?_⟩
    intro assertion member
    exact (extension_translation_exact classes roles (Sum.elim named anonymous)
      membership active assertion.1 (admitted assertion member)
      (Sum.elim named anonymous assertion.2)).mp (h assertion member)
  · rintro ⟨anonymous, h⟩
    refine ⟨anonymous, ?_⟩
    intro assertion member
    exact (extension_translation_exact classes roles (Sum.elim named anonymous)
      membership active assertion.1 (admitted assertion member)
      (Sum.elim named anonymous assertion.2)).mpr (h assertion member)

#print axioms erase_top_data_inclusion
#print axioms anonymous_assignment_translation_exact
end ContextCalculus.FiniteDataMembership
