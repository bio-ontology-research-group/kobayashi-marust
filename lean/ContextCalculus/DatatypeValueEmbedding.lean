import Mathlib.Logic.Function.Basic

/-! Semantic value-carrier embedding. Parsing, datatype membership decisions,
source coverage and worker execution require independent evidence. -/
namespace ContextCalculus.DatatypeValueEmbedding

def ValueConcept {Value Carrier : Type} (embed : Value → Carrier)
    (value : Value) (node : Carrier) : Prop := node = embed value

theorem singleton_equality {Value Carrier : Type} (embed : Value → Carrier)
    (value : Value) (left right : Carrier)
    (hl : ValueConcept embed value left) (hr : ValueConcept embed value right) :
    left = right := hl.trans hr.symm

theorem distinct_values_clash {Value Carrier : Type} (embed : Value → Carrier)
    (injective : Function.Injective embed) (left right : Value) (node : Carrier)
    (different : left ≠ right) :
    ¬ (ValueConcept embed left node ∧ ValueConcept embed right node) := by
  rintro ⟨hl, hr⟩
  exact different (injective (hl.symm.trans hr))

theorem value_concept_equality {Value Carrier : Type} (embed : Value → Carrier)
    (injective : Function.Injective embed) (left right : Value) :
    embed left = embed right ↔ left = right :=
  ⟨fun equality => injective equality, congrArg embed⟩

def EmbeddedRole {Root Value Carrier : Type} (embed : Value → Carrier)
    (role : Root → Value → Prop) (root : Root) (node : Carrier) : Prop :=
  ∃ value, role root value ∧ node = embed value

theorem functional_role_iff {Root Value Carrier : Type} (embed : Value → Carrier)
    (injective : Function.Injective embed) (role : Root → Value → Prop) :
    (∀ root left right, role root left → role root right → left = right) ↔
    (∀ root left right, EmbeddedRole embed role root left →
      EmbeddedRole embed role root right → left = right) := by
  constructor
  · intro functional root left right hl hr
    rcases hl with ⟨lv, hlv, rfl⟩
    rcases hr with ⟨rv, hrv, rfl⟩
    exact congrArg embed (functional root lv rv hlv hrv)
  · intro functional root left right hl hr
    exact injective (functional root (embed left) (embed right)
      ⟨left, hl, rfl⟩ ⟨right, hr, rfl⟩)

/-- A literal restriction is preserved by the injective datatype carrier. -/
theorem has_value_iff {Root Value Carrier : Type} (embed : Value → Carrier)
    (injective : Function.Injective embed) (role : Root → Value → Prop)
    (root : Root) (value : Value) :
    role root value ↔ ∃ node,
      EmbeddedRole embed role root node ∧ ValueConcept embed value node := by
  constructor
  · intro edge
    exact ⟨embed value, ⟨value, edge, rfl⟩, rfl⟩
  · rintro ⟨node, ⟨other, edge, mapped⟩, singleton⟩
    have equal : other = value := injective (mapped.symm.trans singleton)
    exact equal ▸ edge

/-- Alternatives remain alternatives after value embedding. Collecting both
literal names for admission does not require both role edges to hold. -/
theorem disjunctive_has_value_iff {Root Value Carrier : Type}
    (embed : Value → Carrier) (injective : Function.Injective embed)
    (role : Root → Value → Prop) (root : Root) (left right : Value) :
    (role root left ∨ role root right) ↔
      ((∃ node, EmbeddedRole embed role root node ∧ ValueConcept embed left node) ∨
       (∃ node, EmbeddedRole embed role root node ∧ ValueConcept embed right node)) :=
  or_congr (has_value_iff embed injective role root left)
    (has_value_iff embed injective role root right)

/-- The same injective value embedding must be used on both sides of a data
subproperty inclusion. This preserves sharing across property hierarchies. -/
theorem subproperty_iff {Root Value Carrier : Type}
    (embed : Value → Carrier) (injective : Function.Injective embed)
    (sub super : Root → Value → Prop) :
    (∀ root value, sub root value → super root value) ↔
      (∀ root node, EmbeddedRole embed sub root node →
        EmbeddedRole embed super root node) := by
  constructor
  · intro inclusion root node edge
    rcases edge with ⟨value, edge, mapped⟩
    exact ⟨value, inclusion root value edge, mapped⟩
  · intro inclusion root value edge
    obtain ⟨other, superEdge, mapped⟩ :=
      inclusion root (embed value) ⟨value, edge, rfl⟩
    have equal : value = other := injective mapped
    exact equal.symm ▸ superEdge

end ContextCalculus.DatatypeValueEmbedding

#print axioms ContextCalculus.DatatypeValueEmbedding.singleton_equality
#print axioms ContextCalculus.DatatypeValueEmbedding.distinct_values_clash
#print axioms ContextCalculus.DatatypeValueEmbedding.value_concept_equality
#print axioms ContextCalculus.DatatypeValueEmbedding.functional_role_iff

#print axioms ContextCalculus.DatatypeValueEmbedding.has_value_iff
#print axioms ContextCalculus.DatatypeValueEmbedding.disjunctive_has_value_iff

#print axioms ContextCalculus.DatatypeValueEmbedding.subproperty_iff
