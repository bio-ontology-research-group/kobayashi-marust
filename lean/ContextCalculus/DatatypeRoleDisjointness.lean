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

/-- Relocating an edge maps both endpoints. Positive and negative edges may
coexist after relocation exactly when no original conflicting pair acquires
the same two endpoints. No injectivity assumption is appropriate for a merge. -/
def Relocated {Node : Type} (merge : Node → Node)
    (edge : Node → Node → Prop) (source target : Node) : Prop :=
  ∃ oldSource oldTarget, edge oldSource oldTarget ∧
    merge oldSource = source ∧ merge oldTarget = target

theorem relocation_conflict_iff {Node : Type} (merge : Node → Node)
    (positive negative : Node → Node → Prop) :
    (∃ source target, Relocated merge positive source target ∧
      Relocated merge negative source target) ↔
    (∃ ps pt ns nt, positive ps pt ∧ negative ns nt ∧
      merge ps = merge ns ∧ merge pt = merge nt) := by
  constructor
  · rintro ⟨source, target, ⟨ps, pt, hp, hs, ht⟩,
      ⟨ns, nt, hn, hns, hnt⟩⟩
    exact ⟨ps, pt, ns, nt, hp, hn, hs.trans hns.symm, ht.trans hnt.symm⟩
  · rintro ⟨ps, pt, ns, nt, hp, hn, hs, ht⟩
    exact ⟨merge ps, merge pt, ⟨ps, pt, hp, rfl, rfl⟩,
      ⟨ns, nt, hn, hs.symm, ht.symm⟩⟩

end ContextCalculus.DatatypeRoleDisjointness
#print axioms ContextCalculus.DatatypeRoleDisjointness.disjoint_roles_iff
#print axioms ContextCalculus.DatatypeRoleDisjointness.noninjective_mapping_can_break_disjointness
#print axioms ContextCalculus.DatatypeRoleDisjointness.relocation_conflict_iff
