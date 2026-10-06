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

/-- Independent oracle for the finite Boolean controls: each role needs a
nonempty value set, and adjacent roles need disjoint sets. Choosing one value
per set gives a two-coloring; singleton color sets give the reverse model. -/
theorem boolean_witnesses_iff_coloring {Vertex : Type}
    (adjacent : Vertex → Vertex → Prop) :
    (∃ values : Vertex → Bool → Prop,
      (∀ vertex, ∃ value, values vertex value) ∧
      (∀ left right, adjacent left right →
        ∀ value, ¬ (values left value ∧ values right value))) ↔
    (∃ color : Vertex → Bool,
      ∀ left right, adjacent left right → color left ≠ color right) := by
  classical
  constructor
  · rintro ⟨values, inhabited, disjoint⟩
    let color := fun vertex => Classical.choose (inhabited vertex)
    have chosen : ∀ vertex, values vertex (color vertex) :=
      fun vertex => Classical.choose_spec (inhabited vertex)
    refine ⟨color, ?_⟩
    intro left right edge equal
    exact disjoint left right edge (color left)
      ⟨chosen left, equal.symm ▸ chosen right⟩
  · rintro ⟨color, proper⟩
    refine ⟨fun vertex value => value = color vertex, ?_, ?_⟩
    · intro vertex
      exact ⟨color vertex, rfl⟩
    · intro left right edge value both
      exact proper left right edge (both.1.symm.trans both.2)

end ContextCalculus.DatatypeRoleDisjointness
#print axioms ContextCalculus.DatatypeRoleDisjointness.disjoint_roles_iff
#print axioms ContextCalculus.DatatypeRoleDisjointness.noninjective_mapping_can_break_disjointness
#print axioms ContextCalculus.DatatypeRoleDisjointness.relocation_conflict_iff
#print axioms ContextCalculus.DatatypeRoleDisjointness.boolean_witnesses_iff_coloring
