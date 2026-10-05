/-!
A DL-safe rule guarded by an object variable is vacuous when the named-object
domain is empty. Concrete atoms and arithmetic need no evaluation in this case.
This does not apply to ground rules or rules with only data-variable guards.
-/
namespace ContextCalculus.DLSafeEmptyNamedDomain

variable {Object Binding : Type}

def GuardedRule (named : Object → Prop)
    (body head : Object → Binding → Prop) : Prop :=
  ∀ object binding, named object → body object binding → head object binding

theorem guarded_rule_vacuous
    (named : Object → Prop) (body head : Object → Binding → Prop)
    (empty : ∀ object, ¬ named object) : GuardedRule named body head := by
  intro object binding guard
  exact False.elim (empty object guard)

theorem theory_models_preserved
    (base : Prop) (named : Object → Prop) (body head : Object → Binding → Prop)
    (empty : ∀ object, ¬ named object) :
    (base ∧ GuardedRule named body head) ↔ base := by
  constructor
  · exact And.left
  · intro model
    exact ⟨model, guarded_rule_vacuous named body head empty⟩

/-- Whole-family projection, including already vacuous observer constraints.
The index is arbitrary; no finite enumeration or count assumption is needed
for the model equivalence. Frontend coverage separately binds it to all rules. -/
theorem rule_family_models_preserved {Index : Type}
    (base observer : Prop) (named : Object → Prop)
    (body head : Index → Object → Binding → Prop)
    (empty : ∀ object, ¬ named object) (observer_valid : observer) :
    (base ∧ observer ∧ ∀ index, GuardedRule named (body index) (head index)) ↔ base := by
  constructor
  · exact And.left
  · intro model
    exact ⟨model, observer_valid, fun index =>
      guarded_rule_vacuous named (body index) (head index) empty⟩

#print axioms rule_family_models_preserved

#print axioms guarded_rule_vacuous
#print axioms theory_models_preserved
end ContextCalculus.DLSafeEmptyNamedDomain
