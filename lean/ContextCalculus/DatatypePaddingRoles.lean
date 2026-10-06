import ContextCalculus.DatatypePadding

/-! Ordinary-role and nominal obligations of the edgeless padding construction.
Reflexivity is explicitly excluded: adding an edgeless point does not preserve
it. These lemmas do not assert that a parsed input contains only these shapes.
-/
namespace ContextCalculus.DatatypePadding

universe u v w z

theorem role_on_objects {O : Type u} {V : Type v}
    (r : O → O → Prop) (x y : O) :
    objectRole (V := V) r (.inl x) (.inl y) ↔ r x y := Iff.rfl

theorem inverse_role {O : Type u} {V : Type v}
    (r : O → O → Prop) (x y : Sum O V) :
    objectRole (fun a b => r b a) x y ↔ objectRole r y x := by
  cases x <;> cases y <;> rfl

theorem role_inclusion {O : Type u} {V : Type v}
    (r s : O → O → Prop) (included : ∀ x y, r x y → s x y) :
    ∀ x y : Sum O V, objectRole r x y → objectRole s x y := by
  intro x y edge
  cases x <;> cases y
  · exact included _ _ edge
  all_goals exact False.elim edge

theorem role_chain {O : Type u} {V : Type v}
    (r s t : O → O → Prop) (included : ∀ x y z, r x y → s y z → t x z) :
    ∀ x y z : Sum O V, objectRole r x y → objectRole s y z → objectRole t x z := by
  intro x y z first second
  cases x <;> cases y <;> cases z
  · exact included _ _ _ first second
  all_goals first | exact False.elim first | exact False.elim second

theorem role_functionality {O : Type u} {V : Type v}
    (r : O → O → Prop) (functional : ∀ x y z, r x y → r x z → y = z) :
    ∀ x y z : Sum O V, objectRole r x y → objectRole r x z → y = z := by
  intro x y z first second
  cases x <;> cases y <;> cases z
  · exact congrArg Sum.inl (functional _ _ _ first second)
  all_goals first | exact False.elim first | exact False.elim second

theorem role_disjointness {O : Type u} {V : Type v}
    (r s : O → O → Prop) (disjoint : ∀ x y, r x y → s x y → False) :
    ∀ x y : Sum O V, objectRole r x y → objectRole s x y → False := by
  intro x y first second
  cases x <;> cases y
  · exact disjoint _ _ first second
  all_goals exact False.elim first

theorem role_irreflexivity {O : Type u} {V : Type v}
    (r : O → O → Prop) (irreflexive : ∀ x, ¬ r x x) :
    ∀ x : Sum O V, ¬ objectRole r x x := by
  intro x edge
  cases x with
  | inl x => exact irreflexive x edge
  | inr _ => exact edge

theorem role_domain {O : Type u} {V : Type v}
    (r : O → O → Prop) (p : O → Prop) (padding : V → Prop)
    (domain : ∀ x y, r x y → p x) :
    ∀ x y : Sum O V, objectRole r x y → extend p padding x := by
  intro x y edge
  cases x <;> cases y
  · exact domain _ _ edge
  all_goals exact False.elim edge

theorem role_range {O : Type u} {V : Type v}
    (r : O → O → Prop) (p : O → Prop) (padding : V → Prop)
    (range : ∀ x y, r x y → p y) :
    ∀ x y : Sum O V, objectRole r x y → extend p padding y := by
  intro x y edge
  cases x <;> cases y
  · exact range _ _ edge
  all_goals exact False.elim edge

theorem nominal_singleton {O : Type u} {V : Type v}
    (named : O) (node : Sum O V) :
    extend (fun x => x = named) (fun _ => False) node ↔ node = .inl named := by
  cases node <;> simp [extend]

/-- This is why the executable witness must inspect edge-generating RBox
clauses as well as source GCIs before using an edgeless padding type. -/
theorem padding_is_not_reflexive {O : Type u} {V : Type v}
    (r : O → O → Prop) (padding : V) :
    ¬ objectRole r (.inr padding) (.inr padding) := fun impossible => impossible

theorem role_endpoints {O : Type u} {V : Type v}
    (role : O → O → Prop) (a b : Sum O V) (edge : objectRole role a b) :
    ∃ x y, a = Sum.inl x ∧ b = Sum.inl y := by
  cases a <;> cases b
  · exact ⟨_, _, rfl, rfl⟩
  all_goals exact False.elim edge

/-- If role premises cover every variable used by a clause, any matching
assignment in the extension lies entirely in the original object carrier.
The executable checker must establish coverage for body variables as well as
head variables: an unguarded body class can become true only on padding. -/
theorem role_guards_bind_objects {O : Type u} {V : Type v}
    {Role : Type w} {Var : Type z}
    (roles : Role → O → O → Prop) (body : List (Role × Var × Var))
    (assignment : Var → Sum O V) (fallback : O)
    (premises : ∀ atom ∈ body,
      objectRole (roles atom.1) (assignment atom.2.1) (assignment atom.2.2))
    (covered : ∀ index, ∃ role source target,
      (role, source, target) ∈ body ∧ (index = source ∨ index = target)) :
    ∃ original : Var → O, ∀ index, assignment index = .inl (original index) := by
  have points : ∀ index, ∃ object, assignment index = Sum.inl object := by
    intro index
    obtain ⟨role, source, target, member, endpoint⟩ := covered index
    have edge := premises (role, source, target) member
    obtain ⟨x, y, left, right⟩ := role_endpoints (roles role) _ _ edge
    rcases endpoint with atSource | atTarget
    · subst index
      exact ⟨x, left⟩
    · subst index
      exact ⟨y, right⟩
  refine ⟨fun index => match assignment index with
    | .inl object => object
    | .inr _ => fallback, ?_⟩
  intro index
  obtain ⟨object, equal⟩ := points index
  simp [equal]

/-- Covering only head endpoints is insufficient. An otherwise empty body
class can become true on padding and activate a new role conclusion. -/
theorem unguarded_body_counterexample :
    (∀ _x _y _z : Unit, (True ∧ False) → False) ∧
    ¬ (∀ x y z : Sum Unit Unit,
      (objectRole (fun (_ _ : Unit) => True) x y ∧
        extend (fun (_ : Unit) => False) (fun (_ : Unit) => True) z) →
      objectRole (fun (_ _ : Unit) => False) x y) := by
  constructor
  · intro _ _ _ premise
    exact premise.2
  · intro extended
    exact extended (.inl ()) (.inl ()) (.inr ()) ⟨True.intro, True.intro⟩

#print axioms role_on_objects
#print axioms inverse_role
#print axioms role_inclusion
#print axioms role_chain
#print axioms role_functionality
#print axioms role_disjointness
#print axioms role_irreflexivity
#print axioms role_domain
#print axioms role_range
#print axioms nominal_singleton
#print axioms padding_is_not_reflexive
#print axioms role_endpoints
#print axioms role_guards_bind_objects
#print axioms unguarded_body_counterexample

end ContextCalculus.DatatypePadding
