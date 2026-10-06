import ContextCalculus.Hypertableau

/-! Exact semantics of the role-clash shape recognized by the experimental
bridge. This does not certify datatype realization or the completion engine. -/
namespace ContextCalculus.Hypertableau

def roleDisjointClause (left right : Role) (source target : Nat) :
    Clause Nat Concept Role :=
  ⟨[.role left source target, .role right source target], []⟩

theorem roleDisjointClause_iff (I : Interp Domain Concept Role)
    (left right : Role) (source target : Nat) (distinct : source ≠ target) :
    I.modelsClause (roleDisjointClause left right source target) ↔
      ∀ x y, ¬ (I.role left x y ∧ I.role right x y) := by
  constructor
  · intro model x y both
    let assignment := fun n => if n = source then x else y
    have target_ne : target ≠ source := Ne.symm distinct
    have body : ∀ atom ∈ (roleDisjointClause left right source target).body,
        I.satAtom assignment atom := by
      intro atom member
      simp only [roleDisjointClause, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simpa [Interp.satAtom, assignment, target_ne] using both.1
      · simpa [Interp.satAtom, assignment, target_ne] using both.2
    obtain ⟨atom, impossible, _⟩ := model assignment body
    exact List.not_mem_nil impossible
  · intro disjoint assignment body
    have first := body (.role left source target) (by simp [roleDisjointClause])
    have second := body (.role right source target) (by simp [roleDisjointClause])
    exact False.elim (disjoint (assignment source) (assignment target) ⟨first, second⟩)

theorem selfDisjointRole_iff_empty (role : Domain → Domain → Prop) :
    (∀ x y, ¬ (role x y ∧ role x y)) ↔ (∀ x y, ¬ role x y) := by
  constructor
  · intro disjoint x y edge
    exact disjoint x y ⟨edge, edge⟩
  · intro empty x y both
    exact empty x y both.1

theorem inverseRoleDisjoint_iff (left right : Domain → Domain → Prop) :
    (∀ x y, ¬ (left x y ∧ right x y)) ↔
      (∀ x y, ¬ (left y x ∧ right y x)) := by
  constructor <;> intro disjoint x y <;> exact disjoint y x

end ContextCalculus.Hypertableau
#print axioms ContextCalculus.Hypertableau.roleDisjointClause_iff
#print axioms ContextCalculus.Hypertableau.selfDisjointRole_iff_empty
#print axioms ContextCalculus.Hypertableau.inverseRoleDisjoint_iff
