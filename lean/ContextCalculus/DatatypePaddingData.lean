import ContextCalculus.DatatypePadding

/-! Concrete two-sorted role transport for the forward padding construction.
The range predicate is the actual value-space interpretation. Establishing
that a frontend symbol denotes this predicate remains a separate obligation.
-/
namespace ContextCalculus.DatatypePadding

open FunctionalDatatypeQuotient (atLeast)
universe u v

def dataRole {O : Type u} {V : Type v} (role : O → V → Prop) :
    Sum O V → Sum O V → Prop
  | .inl object, .inr value => role object value
  | _, _ => False

def dataRange {O : Type u} {V : Type v} (range : V → Prop) : Sum O V → Prop
  | .inl _ => False
  | .inr value => range value

theorem data_exists_on_objects {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (object : O) :
    (∃ value, role object value ∧ range value) ↔
      ∃ node, dataRole role (.inl object) node ∧ dataRange range node := by
  constructor
  · rintro ⟨value, edge, member⟩
    exact ⟨.inr value, edge, member⟩
  · rintro ⟨node, edge, member⟩
    cases node with
    | inl _ => exact False.elim edge
    | inr value => exact ⟨value, edge, member⟩

theorem data_forall_on_objects {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (object : O) :
    (∀ value, role object value → range value) ↔
      ∀ node, dataRole role (.inl object) node → dataRange range node := by
  constructor
  · intro universal node edge
    cases node with
    | inl _ => exact False.elim edge
    | inr value => exact universal value edge
  · intro universal value edge
    exact universal (.inr value) edge

/-- The fallback is available because the OWL value domain is nonempty. It
is never selected for a witness connected by an actual data edge. -/
theorem data_minimum_on_objects {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (object : O)
    (fallback : V) (n : Nat) :
    atLeast role range object n ↔
      atLeast (dataRole role) (dataRange range) (.inl object) n := by
  constructor
  · rintro ⟨vs, edges, distinct⟩
    refine ⟨fun i => .inr (vs i), ?_, ?_⟩
    · exact edges
    · intro i j equal
      exact distinct i j (Sum.inr.inj equal)
  · rintro ⟨ws, edges, distinct⟩
    let vs : Fin n → V := fun i => match ws i with
      | .inl _ => fallback
      | .inr value => value
    have mapped : ∀ i, ws i = Sum.inr (vs i) := by
      intro i
      cases h : ws i with
      | inl _ =>
          have edge := (edges i).1
          rw [h] at edge
          exact False.elim edge
      | inr value => simp [vs, h]
    refine ⟨vs, ?_, ?_⟩
    · intro i
      have edge := edges i
      rw [mapped i] at edge
      exact edge
    · intro i j equal
      apply distinct i j
      exact (mapped i).trans ((congrArg Sum.inr equal).trans (mapped j).symm)

theorem data_maximum_on_objects {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (object : O)
    (fallback : V) (n : Nat) :
    (¬ atLeast role range object (n+1)) ↔
      ¬ atLeast (dataRole role) (dataRange range) (.inl object) (n+1) :=
  not_congr (data_minimum_on_objects role range object fallback (n+1))

theorem data_exists_on_padding {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (value : V) :
    ¬ ∃ node, dataRole role (.inr value) node ∧ dataRange range node := by
  rintro ⟨_, impossible, _⟩
  exact impossible

theorem data_forall_on_padding {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (value : V) :
    ∀ node, dataRole role (.inr value) node → dataRange range node := by
  intro _ impossible
  exact False.elim impossible

theorem data_minimum_on_padding {O : Type u} {V : Type v}
    (role : O → V → Prop) (range : V → Prop) (value : V) (n : Nat) :
    atLeast (dataRole role) (dataRange range) (.inr value) n ↔ n = 0 := by
  cases n with
  | zero =>
      constructor
      · intro _; rfl
      · intro _
        exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n =>
      constructor
      · rintro ⟨_, edges, _⟩
        exact False.elim (edges ⟨0, Nat.zero_lt_succ n⟩).1
      · intro impossible
        exact False.elim (Nat.noConfusion impossible)

#print axioms data_exists_on_objects
#print axioms data_forall_on_objects
#print axioms data_minimum_on_objects
#print axioms data_maximum_on_objects
#print axioms data_exists_on_padding
#print axioms data_forall_on_padding
#print axioms data_minimum_on_padding

end ContextCalculus.DatatypePadding
