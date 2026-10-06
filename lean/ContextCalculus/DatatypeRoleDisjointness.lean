import ContextCalculus.DatatypeValueEmbedding

/-! A shared injective value embedding preserves data-property disjointness.
This supporting theorem does not supply a runtime value realization or extend
production admission. A counterexample records why arbitrary collapsing of
witness nodes is insufficient. -/
namespace ContextCalculus.DatatypeRoleDisjointness
open ContextCalculus.DatatypeValueEmbedding

theorem disjoint_roles_iff {Root Value Carrier : Type}
    (embed : Value → Carrier) (injective : Function.Injective embed)
    (left right : Root → Value → Prop) :
    (∀ root value, ¬ (left root value ∧ right root value)) ↔
    (∀ root node, ¬ (EmbeddedRole embed left root node ∧
      EmbeddedRole embed right root node)) := by
  constructor
  · intro disjoint root node both
    obtain ⟨lv, hl, mappedLeft⟩ := both.1
    obtain ⟨rv, hr, mappedRight⟩ := both.2
    have equal : lv = rv := injective (mappedLeft.symm.trans mappedRight)
    subst rv
    exact disjoint root lv ⟨hl, hr⟩
  · intro disjoint root value both
    exact disjoint root (embed value)
      ⟨⟨value, both.1, rfl⟩, ⟨value, both.2, rfl⟩⟩

/-- Two disjoint singleton value sets become overlapping if both values are
mapped to the same node. This is not an admissible realization. -/
theorem noninjective_mapping_can_break_disjointness :
    (∀ value : Bool, ¬ (value = false ∧ value = true)) ∧
    ¬ (∀ node : Unit,
      ¬ (EmbeddedRole (fun _ : Bool => ()) (fun _ : Unit => fun v => v = false) () node ∧
         EmbeddedRole (fun _ : Bool => ()) (fun _ : Unit => fun v => v = true) () node)) := by
  constructor
  · intro value both
    cases value <;> simp_all
  · intro disjoint
    exact disjoint () ⟨⟨false, rfl, rfl⟩, ⟨true, rfl, rfl⟩⟩

end ContextCalculus.DatatypeRoleDisjointness
#print axioms ContextCalculus.DatatypeRoleDisjointness.disjoint_roles_iff
#print axioms ContextCalculus.DatatypeRoleDisjointness.noninjective_mapping_can_break_disjointness
