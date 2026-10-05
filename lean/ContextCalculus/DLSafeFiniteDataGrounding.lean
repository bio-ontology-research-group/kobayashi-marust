/-!
Finite data grounding is justified by restricting a model's data extension,
not by assuming missing assertions are false. This boundary requires positive
data body atoms, unchanged object heads, and coverage of every data variable.
Source admission must separately prove absence of value-generating axioms.
-/
namespace ContextCalculus.DLSafeFiniteDataGrounding
variable {Property Object Data Binding : Type}

def restrictData (role : Property → Object → Data → Prop)
    (selected : Data → Prop) : Property → Object → Data → Prop :=
  fun property object value => role property object value ∧ selected value

theorem preserves_assertion (role : Property → Object → Data → Prop)
    (selected : Data → Prop) (property : Property) (object : Object) (value : Data)
    (assertion : role property object value) (retained : selected value) :
    restrictData role selected property object value := ⟨assertion, retained⟩

theorem preserves_domain (role : Property → Object → Data → Prop)
    (selected : Data → Prop) (property : Property) (domain : Object → Prop)
    (source : ∀ object value, role property object value → domain object) :
    ∀ object value, restrictData role selected property object value → domain object := by
  intro object value fact
  exact source object value fact.1

theorem preserves_range (role : Property → Object → Data → Prop)
    (selected : Data → Prop) (property : Property) (range : Data → Prop)
    (source : ∀ object value, role property object value → range value) :
    ∀ object value, restrictData role selected property object value → range value := by
  intro object value fact
  exact source object value fact.1

theorem preserves_functionality (role : Property → Object → Data → Prop)
    (selected : Data → Prop) (property : Property)
    (source : ∀ object left right, role property object left →
      role property object right → left = right) :
    ∀ object left right, restrictData role selected property object left →
      restrictData role selected property object right → left = right := by
  intro object left right hl hr
  exact source object left right hl.1 hr.1

structure DataAtom (Property Object Binding : Type) (n : Nat) where
  property : Property
  subject : Binding → Object
  dataIndex : Fin n

def dataBody {n m : Nat} (atoms : Fin m → DataAtom Property Object Binding n)
    (role : Property → Object → Data → Prop) (binding : Binding)
    (values : Fin n → Data) : Prop :=
  ∀ index, role (atoms index).property ((atoms index).subject binding)
    (values (atoms index).dataIndex)

def sourceRule {n m : Nat} (atoms : Fin m → DataAtom Property Object Binding n)
    (role : Property → Object → Data → Prop)
    (objectBody head : Binding → Prop) (tests : (Fin n → Data) → Prop) : Prop :=
  ∀ binding values, objectBody binding → tests values →
    dataBody atoms role binding values → head binding

theorem preserves_object_head_rule {n m : Nat}
    (atoms : Fin m → DataAtom Property Object Binding n)
    (role : Property → Object → Data → Prop) (selected : Data → Prop)
    (objectBody head : Binding → Prop) (tests : (Fin n → Data) → Prop)
    (source : sourceRule atoms role objectBody head tests) :
    sourceRule atoms (restrictData role selected) objectBody head tests := by
  intro binding values objects concrete facts
  apply source binding values objects concrete
  intro index
  exact (facts index).1

/-- On a restricted extension, covering every variable by a positive data atom
makes finite grounding equivalent to universal rule satisfaction. Tests can
include arbitrary builtin relations and shared tuple constraints. -/
theorem finite_grounding_iff {n m : Nat}
    (atoms : Fin m → DataAtom Property Object Binding n)
    (covered : ∀ dataIndex, ∃ index, (atoms index).dataIndex = dataIndex)
    (role : Property → Object → Data → Prop) (selected : Data → Prop)
    (objectBody head : Binding → Prop) (tests : (Fin n → Data) → Prop) :
    sourceRule atoms (restrictData role selected) objectBody head tests ↔
      (∀ binding values, (∀ dataIndex, selected (values dataIndex)) →
        objectBody binding → tests values →
        dataBody atoms role binding values → head binding) := by
  constructor
  · intro source binding values chosen objects concrete facts
    apply source binding values objects concrete
    intro index
    exact ⟨facts index, chosen (atoms index).dataIndex⟩
  · intro grounded binding values objects concrete facts
    have chosen : ∀ dataIndex, selected (values dataIndex) := by
      intro dataIndex
      obtain ⟨index, equality⟩ := covered dataIndex
      rw [← equality]
      exact (facts index).2
    exact grounded binding values chosen objects concrete (fun index => (facts index).1)

/-- Existence of a model is preserved when the base theory permits data
restriction. Object interpretations and query truth are held fixed, so this
also applies separately to each classification countermodel obligation. -/
theorem model_existence_iff_restricted_rules {n m : Nat}
    (atoms : Fin m → DataAtom Property Object Binding n)
    (selected : Data → Prop)
    (base : (Property → Object → Data → Prop) → Prop)
    (restrictionClosed : ∀ role, base role → base (restrictData role selected))
    (objectBody head : Binding → Prop) (tests : (Fin n → Data) → Prop) :
    (∃ role, base role ∧ sourceRule atoms role objectBody head tests) ↔
    (∃ role, base role ∧ sourceRule atoms (restrictData role selected) objectBody head tests) := by
  constructor
  · rintro ⟨role, hbase, hrule⟩
    exact ⟨role, hbase, preserves_object_head_rule atoms role selected objectBody head tests hrule⟩
  · rintro ⟨role, hbase, hrule⟩
    exact ⟨restrictData role selected, restrictionClosed role hbase, hrule⟩

#print axioms model_existence_iff_restricted_rules
#print axioms preserves_assertion
#print axioms preserves_domain
#print axioms preserves_range
#print axioms preserves_functionality
#print axioms preserves_object_head_rule
#print axioms finite_grounding_iff

/-- Adding only consequences whose complete positive premises are already
proved preserves every source model. The original rule is retained. This
does not assert that forward chaining computes every entailed assertion. -/
theorem positive_assertion_consequence {Atom : Type}
    (holds : Atom → Prop) (known : Atom → Prop)
    (sound : ∀ atom, known atom → holds atom)
    (body : List Atom) (head : Atom)
    (rule : (∀ atom ∈ body, holds atom) → holds head)
    (premises : ∀ atom ∈ body, known atom) :
    ∀ atom, (known atom ∨ atom = head) → holds atom := by
  intro atom added
  rcases added with old | equality
  · exact sound atom old
  · subst atom
    exact rule (fun atom membership => sound atom (premises atom membership))

#print axioms positive_assertion_consequence

/-- A transitive-role rule adds no constraint when its head is precisely the
two-edge composition already entailed by the source RBox. Additional body
guards, including inequalities, do not invalidate this implication. -/
theorem transitive_rule_redundant
    (role : Object → Object → Prop)
    (transitive : ∀ x y z, role x y → role y z → role x z)
    (left middle right : Binding → Object) (extra : Binding → Prop) :
    ∀ binding, extra binding → role (left binding) (middle binding) →
      role (middle binding) (right binding) → role (left binding) (right binding) := by
  intro binding _ first second
  exact transitive _ _ _ first second

#print axioms transitive_rule_redundant

/-- A negative named role assertion is exactly the empty-head clause guarded
by its two singleton nominal concepts. Equality of the two names is allowed. -/
theorem negative_role_nominal_constraint
    (role : Object → Object → Prop) (left right : Object)
    (leftNominal rightNominal : Object → Prop)
    (leftSingleton : ∀ x, leftNominal x ↔ x = left)
    (rightSingleton : ∀ x, rightNominal x ↔ x = right) :
    (∀ x y, leftNominal x → rightNominal y → role x y → False) ↔
      ¬role left right := by
  constructor
  · intro constraint edge
    exact constraint left right ((leftSingleton left).mpr rfl)
      ((rightSingleton right).mpr rfl) edge
  · intro negative x y namedLeft namedRight edge
    have hx := (leftSingleton x).mp namedLeft
    have hy := (rightSingleton y).mp namedRight
    rw [hx, hy] at edge
    exact negative edge

#print axioms negative_role_nominal_constraint
end ContextCalculus.DLSafeFiniteDataGrounding
