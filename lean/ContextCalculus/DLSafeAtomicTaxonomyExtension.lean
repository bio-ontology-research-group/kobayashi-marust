/-! Conditional class-query countermodels for a DL-safe named graph. The
source gate must establish pointwise class constraints and graph-extension
preservation. This does not certify a graph evaluator or arbitrary OWL axioms. -/
namespace ContextCalculus.DLSafeAtomicTaxonomyExtension

structure Model (Class Role Object : Type) where
  concept : Class → Object → Prop
  role : Role → Object → Object → Prop

def extend {Class Role Object : Type} (model : Model Class Role Object)
    (valuation : Class → Prop) : Model Class Role (Option Object) where
  concept := fun name x => match x with
    | some old => model.concept name old
    | none => valuation name
  role := fun role x y => match x, y with
    | some old, some target => model.role role old target
    | _, _ => False

def pointwise {Class Role Object : Type} (model : Model Class Role Object)
    (constraint : (Class → Prop) → Prop) : Prop :=
  ∀ x, constraint (fun name => model.concept name x)

theorem pointwise_extension {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (constraint : (Class → Prop) → Prop)
    (oldValid : pointwise model constraint) (freshValid : constraint valuation) :
    pointwise (extend model valuation) constraint := by
  intro x
  cases x with
  | none => exact freshValid
  | some old => exact oldValid old

theorem named_edges_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (role : Role) (x y : Object) :
    (extend model valuation).role role (some x) (some y) ↔ model.role role x y := Iff.rfl

theorem named_classes_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (name : Class) (x : Object) :
    (extend model valuation).concept name (some x) ↔ model.concept name x := Iff.rfl

theorem taxonomy_countermodel {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (constraint : (Class → Prop) → Prop)
    (graphValid : Model Class Role (Option Object) → Prop)
    (oldValid : pointwise model constraint) (freshValid : constraint valuation)
    (graphExtension : graphValid (extend model valuation))
    (left right : Class) (hasLeft : valuation left) (lacksRight : ¬valuation right) :
    ∃ witness : Model Class Role (Option Object),
      pointwise witness constraint ∧ graphValid witness ∧
      ∃ x, witness.concept left x ∧ ¬witness.concept right x := by
  exact ⟨extend model valuation,
    pointwise_extension model valuation constraint oldValid freshValid,
    graphExtension, none, hasLeft, lacksRight⟩

/- Publication applies to both A → B and ¬ A queries. It requires an actual
original-source model and preservation for every admitted fresh valuation. -/
theorem boolean_query_projection_exact {Class Role Object : Type}
    (model : Model Class Role Object)
    (constraint query : (Class → Prop) → Prop)
    (graphValid : Model Class Role (Option Object) → Prop)
    (oldValid : pointwise model constraint)
    (extension : ∀ valuation, constraint valuation → graphValid (extend model valuation)) :
    (∀ full : Model Class Role (Option Object),
      pointwise full constraint → graphValid full → pointwise full query) ↔
    (∀ valuation, constraint valuation → query valuation) := by
  constructor
  · intro fullQuery valuation valid
    exact fullQuery (extend model valuation)
      (pointwise_extension model valuation constraint oldValid valid)
      (extension valuation valid) none
  · intro projected full valid _ x
    exact projected (fun name => full.concept name x) (valid x)

theorem domain_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (role : Role) (name : Class)
    (valid : ∀ x y, model.role role x y → model.concept name x) :
    ∀ x y, (extend model valuation).role role x y →
      (extend model valuation).concept name x := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem transitivity_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (role : Role)
    (valid : ∀ x y z, model.role role x y → model.role role y z → model.role role x z) :
    ∀ x y z, (extend model valuation).role role x y →
      (extend model valuation).role role y z → (extend model valuation).role role x z := by
  intro x y z first second
  cases x with
  | none => exact False.elim first
  | some old =>
    cases y with
    | none => exact False.elim first
    | some middle =>
      cases z with
      | none => exact False.elim second
      | some target => exact valid old middle target first second

theorem functionality_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (role : Role)
    (valid : ∀ x y z, model.role role x y → model.role role x z → y = z) :
    ∀ x y z, (extend model valuation).role role x y →
      (extend model valuation).role role x z → y = z := by
  intro x y z first second
  cases x with
  | none => exact False.elim first
  | some old =>
    cases y with
    | none => exact False.elim first
    | some left =>
      cases z with
      | none => exact False.elim second
      | some right => exact congrArg some (valid old left right first second)

theorem inclusion_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (left right : Role)
    (valid : ∀ x y, model.role left x y → model.role right x y) :
    ∀ x y, (extend model valuation).role left x y →
      (extend model valuation).role right x y := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem inverse_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (left right : Role)
    (valid : ∀ x y, model.role left x y ↔ model.role right y x) :
    ∀ x y, (extend model valuation).role left x y ↔
      (extend model valuation).role right y x := by
  intro x y
  cases x with
  | none => cases y <;> exact Iff.rfl
  | some old =>
    cases y with
    | none => exact Iff.rfl
    | some target => exact valid old target

inductive NamedAtom (Class Role Name : Type) where
  | concept (className : Class) (name : Name)
  | role (roleName : Role) (left right : Name)
  | same (left right : Name)
  | different (left right : Name)

def namedHolds {Class Role Name Object : Type} (model : Model Class Role Object)
    (names : Name → Object) : NamedAtom Class Role Name → Prop
  | .concept c n => model.concept c (names n)
  | .role r a b => model.role r (names a) (names b)
  | .same a b => names a = names b
  | .different a b => names a ≠ names b

/-- Names retain their original denotations, including non-unique names. -/
theorem named_atoms_preserved {Class Role Name Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (names : Name → Object) (atom : NamedAtom Class Role Name) :
    namedHolds (extend model valuation) (fun n => some (names n)) atom ↔
      namedHolds model names atom := by
  cases atom with
  | concept c n => exact Iff.rfl
  | role r a b => exact Iff.rfl
  | same a b => exact ⟨Option.some.inj, congrArg some⟩
  | different a b =>
    constructor
    · intro distinct equal
      exact distinct (congrArg some equal)
    · intro distinct equal
      exact distinct (Option.some.inj equal)

def namedRule {Class Role Name Object : Type} (model : Model Class Role Object)
    (names : Name → Object) (body head : List (NamedAtom Class Role Name)) : Prop :=
  (∀ atom ∈ body, namedHolds model names atom) →
    ∀ atom ∈ head, namedHolds model names atom

theorem named_rule_preserved {Class Role Name Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (names : Name → Object) (body head : List (NamedAtom Class Role Name))
    (valid : namedRule model names body head) :
    namedRule (extend model valuation) (fun n => some (names n)) body head := by
  intro premises atom member
  apply (named_atoms_preserved model valuation names atom).mpr
  apply valid _ atom member
  intro premise inBody
  exact (named_atoms_preserved model valuation names premise).mp (premises premise inBody)

def extendData {Property Object Data : Type}
    (source : Property → Object → Data → Prop) : Property → Option Object → Data → Prop :=
  fun property object value => match object with
    | some old => source property old value
    | none => False

theorem data_range_preserved {Property Object Data : Type}
    (source : Property → Object → Data → Prop) (property : Property)
    (range : Data → Prop)
    (valid : ∀ x value, source property x value → range value) :
    ∀ x value, extendData source property x value → range value := by
  intro x value fact
  cases x with
  | none => exact False.elim fact
  | some old => exact valid old value fact

theorem data_functionality_preserved {Property Object Data : Type}
    (source : Property → Object → Data → Prop) (property : Property)
    (valid : ∀ x a b, source property x a → source property x b → a = b) :
    ∀ x a b, extendData source property x a → extendData source property x b → a = b := by
  intro x a b first second
  cases x with
  | none => exact False.elim first
  | some old => exact valid old a b first second

/-- The fixed guard can include concrete data atoms and arithmetic tests.
Their truth must be preserved separately by the data extension; no builtin
is interpreted or discarded by this theorem. -/
theorem guarded_named_rules_preserved {Class Role Name Object Binding : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (names : Binding → Name → Object) (guard : Binding → Prop)
    (body head : List (NamedAtom Class Role Name))
    (valid : ∀ binding, guard binding → namedRule model (names binding) body head) :
    ∀ binding, guard binding →
      namedRule (extend model valuation) (fun n => some (names binding n)) body head := by
  intro binding matched
  exact named_rule_preserved model valuation (names binding) body head (valid binding matched)


/-- Range constraints do not constrain the isolated class-query witness. -/
theorem range_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (role : Role) (name : Class)
    (valid : ∀ x y, model.role role x y → model.concept name y) :
    ∀ x y, (extend model valuation).role role x y →
      (extend model valuation).concept name y := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem inverse_functionality_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (role : Role)
    (valid : ∀ x y z, model.role role x z → model.role role y z → x = y) :
    ∀ x y z, (extend model valuation).role role x z →
      (extend model valuation).role role y z → x = y := by
  intro x y z first second
  cases x with
  | none => exact False.elim first
  | some left =>
    cases z with
    | none => exact False.elim first
    | some target =>
      cases y with
      | none => exact False.elim second
      | some right => exact congrArg some (valid left right target first second)

theorem symmetry_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (role : Role)
    (valid : ∀ x y, model.role role x y → model.role role y x) :
    ∀ x y, (extend model valuation).role role x y →
      (extend model valuation).role role y x := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem asymmetry_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (role : Role)
    (valid : ∀ x y, model.role role x y → ¬model.role role y x) :
    ∀ x y, (extend model valuation).role role x y →
      ¬(extend model valuation).role role y x := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem irreflexivity_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (role : Role)
    (valid : ∀ x, ¬model.role role x x) :
    ∀ x, ¬(extend model valuation).role role x x := by
  intro x
  cases x with
  | none => exact id
  | some old => exact valid old

theorem disjoint_roles_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (left right : Role)
    (valid : ∀ x y, model.role left x y → ¬model.role right x y) :
    ∀ x y, (extend model valuation).role left x y →
      ¬(extend model valuation).role right x y := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem data_domain_preserved {Class Role Property Object Data : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (source : Property → Object → Data → Prop) (property : Property) (name : Class)
    (valid : ∀ x value, source property x value → model.concept name x) :
    ∀ x value, extendData source property x value →
      (extend model valuation).concept name x := by
  intro x value edge
  cases x with
  | none => exact False.elim edge
  | some old => exact valid old value edge

/-- Boolean class expressions are the only TBox constructors admitted by
this projection. Top and bottom have fixed meanings, not arbitrary labels. -/
inductive BooleanClass (Class : Type) where
  | atom (name : Class)
  | top
  | bottom
  | complement (body : BooleanClass Class)
  | conjunction (left right : BooleanClass Class)
  | disjunction (left right : BooleanClass Class)

def booleanHolds {Class : Type} (valuation : Class → Prop) : BooleanClass Class → Prop
  | .atom name => valuation name
  | .top => True
  | .bottom => False
  | .complement body => ¬booleanHolds valuation body
  | .conjunction left right => booleanHolds valuation left ∧ booleanHolds valuation right
  | .disjunction left right => booleanHolds valuation left ∨ booleanHolds valuation right

theorem boolean_old_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (expression : BooleanClass Class) (object : Object) :
    booleanHolds (fun name => (extend model valuation).concept name (some object)) expression ↔
      booleanHolds (fun name => model.concept name object) expression := Iff.rfl

theorem boolean_fresh_valuation {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (expression : BooleanClass Class) :
    booleanHolds (fun name => (extend model valuation).concept name none) expression ↔
      booleanHolds valuation expression := Iff.rfl


def rolePath {Role Object : Type} (relation : Role → Object → Object → Prop) :
    List Role → Object → Object → Prop
  | [], x, y => x = y
  | r :: rs, x, y => ∃ z, relation r x z ∧ rolePath relation rs z y

theorem role_path_old_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (roles : List Role)
    (x y : Object) :
    rolePath (extend model valuation).role roles (some x) (some y) ↔
      rolePath model.role roles x y := by
  induction roles generalizing x with
  | nil => exact ⟨Option.some.inj, congrArg some⟩
  | cons r rs ih =>
    constructor
    · rintro ⟨z, edge, rest⟩
      cases z with
      | none => exact False.elim edge
      | some old => exact ⟨old, edge, (ih old).mp rest⟩
    · rintro ⟨z, edge, rest⟩
      exact ⟨some z, edge, (ih z).mpr rest⟩

theorem role_path_cannot_end_fresh {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop) (roles : List Role)
    (x : Object) : ¬rolePath (extend model valuation).role roles (some x) none := by
  induction roles generalizing x with
  | nil => intro impossible; cases impossible
  | cons r rs ih =>
    rintro ⟨z, edge, rest⟩
    cases z with
    | none => exact edge
    | some old => exact ih old rest

/-- Every nonempty chain stays inside the old graph. Inverse expressions
are interpreted as reversed source relations before applying this theorem. -/
theorem role_chain_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (first : Role) (rest : List Role) (head : Role)
    (valid : ∀ x y, rolePath model.role (first :: rest) x y → model.role head x y) :
    ∀ x y, rolePath (extend model valuation).role (first :: rest) x y →
      (extend model valuation).role head x y := by
  intro x y path
  cases x with
  | none =>
    rcases path with ⟨z, edge, _⟩
    cases z <;> exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim (role_path_cannot_end_fresh model valuation _ old path)
    | some target =>
      exact valid old target ((role_path_old_preserved model valuation _ old target).mp path)


theorem boolean_domain_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (role : Role) (expression : BooleanClass Class)
    (valid : ∀ x y, model.role role x y →
      booleanHolds (fun name => model.concept name x) expression) :
    ∀ x y, (extend model valuation).role role x y →
      booleanHolds (fun name => (extend model valuation).concept name x) expression := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem boolean_range_preserved {Class Role Object : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (role : Role) (expression : BooleanClass Class)
    (valid : ∀ x y, model.role role x y →
      booleanHolds (fun name => model.concept name y) expression) :
    ∀ x y, (extend model valuation).role role x y →
      booleanHolds (fun name => (extend model valuation).concept name y) expression := by
  intro x y edge
  cases x with
  | none => exact False.elim edge
  | some old =>
    cases y with
    | none => exact False.elim edge
    | some target => exact valid old target edge

theorem boolean_data_domain_preserved {Class Role Property Object Data : Type}
    (model : Model Class Role Object) (valuation : Class → Prop)
    (source : Property → Object → Data → Prop) (property : Property)
    (expression : BooleanClass Class)
    (valid : ∀ x value, source property x value →
      booleanHolds (fun name => model.concept name x) expression) :
    ∀ x value, extendData source property x value →
      booleanHolds (fun name => (extend model valuation).concept name x) expression := by
  intro x value edge
  cases x with
  | none => exact False.elim edge
  | some old => exact valid old value edge

#print axioms boolean_domain_preserved
#print axioms boolean_range_preserved
#print axioms boolean_data_domain_preserved
#print axioms role_path_old_preserved
#print axioms role_path_cannot_end_fresh
#print axioms role_chain_preserved
#print axioms range_preserved
#print axioms inverse_functionality_preserved
#print axioms symmetry_preserved
#print axioms asymmetry_preserved
#print axioms irreflexivity_preserved
#print axioms disjoint_roles_preserved
#print axioms data_domain_preserved
#print axioms boolean_old_preserved
#print axioms boolean_fresh_valuation
#print axioms data_range_preserved
#print axioms data_functionality_preserved
#print axioms guarded_named_rules_preserved
#print axioms inclusion_preserved
#print axioms inverse_preserved
#print axioms named_atoms_preserved
#print axioms named_rule_preserved
#print axioms domain_preserved
#print axioms transitivity_preserved
#print axioms functionality_preserved
#print axioms pointwise_extension
#print axioms named_edges_preserved
#print axioms named_classes_preserved
#print axioms taxonomy_countermodel
#print axioms boolean_query_projection_exact
end ContextCalculus.DLSafeAtomicTaxonomyExtension
