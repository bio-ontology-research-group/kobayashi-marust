/-!
Sound named-edge projections used by frontend/abox_consistency.rs.
The source parser and source-to-predicate interpretation remain boundary
premises. These lemmas justify only union antecedents and intersection
consequents, not their converse directions or an unsupported rule evaluator.
-/
namespace ContextCalculus.ABoxBooleanInclusion
variable {Domain Index : Type}

def Included (left right : Domain → Prop) : Prop := ∀ x, left x → right x

theorem union_operand_included (parts : Index → Domain → Prop)
    (right : Domain → Prop) (i : Index)
    (source : Included (fun x => ∃ j, parts j x) right) :
    Included (parts i) right := by
  intro x hx
  exact source x ⟨i, hx⟩

theorem intersection_operand_included (left : Domain → Prop)
    (parts : Index → Domain → Prop) (i : Index)
    (source : Included left (fun x => ∀ j, parts j x)) :
    Included left (parts i) := by
  intro x hx
  exact source x hx i

theorem equivalence_directions (left right : Domain → Prop)
    (source : ∀ x, left x ↔ right x) :
    Included left right ∧ Included right left := by
  exact ⟨fun x hx => (source x).mp hx, fun x hx => (source x).mpr hx⟩

theorem inclusion_transitive (first middle last : Domain → Prop)
    (left : Included first middle) (right : Included middle last) :
    Included first last := by
  intro x hx
  exact right x (left x hx)

/-- An asserted class below two disjoint classes makes the whole source false.
Additional axioms, including uninterpreted rule constraints, cannot restore it. -/
theorem asserted_disjoint_clash (asserted left right : Domain → Prop)
    (individual : Domain) (member : asserted individual)
    (toLeft : Included asserted left) (toRight : Included asserted right)
    (disjoint : ∀ x, left x → right x → False) : False := by
  exact disjoint individual (toLeft individual member) (toRight individual member)

theorem inconsistent_subset (base additional : Prop) (clash : base → False) :
    ¬ (base ∧ additional) := by
  intro full
  exact clash full.1

#print axioms union_operand_included
#print axioms intersection_operand_included
#print axioms equivalence_directions
#print axioms inclusion_transitive
#print axioms asserted_disjoint_clash
#print axioms inconsistent_subset
end ContextCalculus.ABoxBooleanInclusion
