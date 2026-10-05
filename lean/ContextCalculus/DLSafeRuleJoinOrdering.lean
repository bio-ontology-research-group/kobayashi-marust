/-! Join planning permutes ordinary relational body atoms and leaves heads and
bindings unchanged. The runtime excludes atoms whose procedural handling
is order-sensitive. This boundary also covers seeded substitutions through
an unchanged binding guard. -/
namespace ContextCalculus.DLSafeRuleJoinOrdering
variable {Index Binding : Type}

theorem conjunction_reorder_iff (holds : Index → Prop) (order : Index → Index)
    (covers : ∀ index, ∃ position, order position = index) :
    (∀ index, holds index) ↔ (∀ position, holds (order position)) := by
  constructor
  · intro all position
    exact all (order position)
  · intro reordered index
    obtain ⟨position, equality⟩ := covers index
    rw [← equality]
    exact reordered position

theorem rule_instances_preserved (holds : Binding → Index → Prop)
    (guard head : Binding → Prop) (order : Index → Index)
    (covers : ∀ index, ∃ position, order position = index) :
    (∀ binding, guard binding → (∀ index, holds binding index) → head binding) ↔
    (∀ binding, guard binding → (∀ position, holds binding (order position)) → head binding) := by
  constructor
  · intro source binding guarded reordered
    exact source binding guarded ((conjunction_reorder_iff (holds binding) order covers).mpr reordered)
  · intro planned binding guarded original
    exact planned binding guarded ((conjunction_reorder_iff (holds binding) order covers).mp original)

/- A partial binding denotes all of its complete extensions. The independent
source-model checker may discard this whole branch only when a premise is
false on every extension, or the complete head is true on every extension.
The Rust checker establishes these conditions using bound concrete guards
and heads whose object arguments are already bound. -/
theorem reject_false_premise (extendsBinding body head : Binding → Prop)
    (refuted : ∀ binding, extendsBinding binding → ¬ body binding) :
    ∀ binding, extendsBinding binding → body binding → head binding := by
  intro binding extension premise
  exact False.elim (refuted binding extension premise)

theorem accept_true_head (extendsBinding body head : Binding → Prop)
    (satisfied : ∀ binding, extendsBinding binding → head binding) :
    ∀ binding, extendsBinding binding → body binding → head binding := by
  intro binding extension _
  exact satisfied binding extension

theorem class_domain_restriction (body head allowed : Binding → Prop)
    (necessary : ∀ binding, body binding → allowed binding) :
    (∀ binding, body binding → head binding) ↔
    (∀ binding, allowed binding → body binding → head binding) := by
  constructor
  · intro checked binding _ premise
    exact checked binding premise
  · intro checked binding premise
    exact checked binding (necessary binding premise) premise

#print axioms reject_false_premise
#print axioms accept_true_head
#print axioms class_domain_restriction
#print axioms conjunction_reorder_iff
#print axioms rule_instances_preserved
end ContextCalculus.DLSafeRuleJoinOrdering
