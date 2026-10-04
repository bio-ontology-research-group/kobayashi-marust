import Mathlib.Tactic

/-! Concrete disjoint object-domain extension for local concepts and exact
qualified cardinalities. Universal roles and nominals are intentionally absent;
the frontend planner rejects them, including occurrences nested in fillers. -/
namespace ContextCalculus.IsolatedObjectModelExtension

inductive Concept (Class Role : Type) where
  | top | bottom
  | atom (name : Class)
  | neg (inner : Concept Class Role)
  | and (left right : Concept Class Role)
  | or (left right : Concept Class Role)
  | some (role : Role) (filler : Concept Class Role)
  | all (role : Role) (filler : Concept Class Role)
  | min (n : Nat) (role : Role) (filler : Concept Class Role)
  | max (n : Nat) (role : Role) (filler : Concept Class Role)
  | self (role : Role)

structure Model (Class Role Object : Type) where
  concept : Class → Object → Prop
  role : Role → Object → Object → Prop

def count {Object : Type} (predicate : Object → Prop) (n : Nat) : Prop :=
  ∃ witnesses : Fin n → Object, Function.Injective witnesses ∧ ∀ i, predicate (witnesses i)

def holds {Class Role Object : Type} (model : Model Class Role Object)
    : Concept Class Role → Object → Prop
  | .top, _ => True
  | .bottom, _ => False
  | .atom name, x => model.concept name x
  | .neg inner, x => ¬holds model inner x
  | .and left right, x => holds model left x ∧ holds model right x
  | .or left right, x => holds model left x ∨ holds model right x
  | .some role filler, x => ∃ y, model.role role x y ∧ holds model filler y
  | .all role filler, x => ∀ y, model.role role x y → holds model filler y
  | .min n role filler, x => count (fun y => model.role role x y ∧ holds model filler y) n
  | .max n role filler, x => ¬count (fun y => model.role role x y ∧ holds model filler y) (n + 1)
  | .self role, x => model.role role x x

def extend {Class Role Object Fresh : Type} (model : Model Class Role Object)
    : Model Class Role (Sum Object Fresh) where
  concept := fun name x => match x with | .inl old => model.concept name old | .inr _ => False
  role := fun role x y => match x, y with
    | .inl old, .inl target => model.role role old target
    | _, _ => False

theorem count_transport {Object Target : Type} (embed : Object → Target)
    (injective : Function.Injective embed) (predicate : Object → Prop)
    (targetPredicate : Target → Prop)
    (preserved : ∀ x, targetPredicate (embed x) ↔ predicate x)
    (supported : ∀ y, targetPredicate y → ∃ x, embed x = y) (n : Nat) :
    count targetPredicate n ↔ count predicate n := by
  classical
  constructor
  · rintro ⟨witnesses, distinct, matched⟩
    have supportedWitness : ∀ i, ∃ x, embed x = witnesses i := fun i => supported _ (matched i)
    let oldWitness := fun i => Classical.choose (supportedWitness i)
    have mapped : ∀ i, embed (oldWitness i) = witnesses i := fun i => Classical.choose_spec (supportedWitness i)
    refine ⟨oldWitness, ?_, ?_⟩
    · intro i j equal
      apply distinct
      rw [←mapped i, ←mapped j, equal]
    · intro i
      apply (preserved (oldWitness i)).mp
      rw [mapped i]
      exact matched i
  · rintro ⟨witnesses, distinct, matched⟩
    exact ⟨embed ∘ witnesses, injective.comp distinct, fun i => (preserved _).mpr (matched i)⟩

theorem old_concepts_preserved {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (concept : Concept Class Role) (x : Object) :
    holds (extend (Fresh := Fresh) model) concept (.inl x) ↔ holds model concept x := by
  induction concept generalizing x with
  | top | bottom | atom | self => rfl
  | neg inner ih => exact not_congr (ih x)
  | and left right ihLeft ihRight => exact and_congr (ihLeft x) (ihRight x)
  | or left right ihLeft ihRight => exact or_congr (ihLeft x) (ihRight x)
  | some role filler ih =>
    constructor
    · rintro ⟨y, edge, matched⟩
      cases y with
      | inl old => exact ⟨old, edge, (ih old).mp matched⟩
      | inr fresh => exact False.elim edge
    · rintro ⟨y, edge, matched⟩
      exact ⟨.inl y, edge, (ih y).mpr matched⟩
  | all role filler ih =>
    constructor
    · intro matched y edge
      exact (ih y).mp (matched (.inl y) edge)
    · intro matched y edge
      cases y with
      | inl old => exact (ih old).mpr (matched old edge)
      | inr fresh => exact False.elim edge
  | min n role filler ih =>
    apply count_transport Sum.inl Sum.inl_injective
    · intro y
      exact and_congr Iff.rfl (ih y)
    · intro y edge
      cases y with
      | inl old => exact ⟨old, rfl⟩
      | inr fresh => exact False.elim edge.1
  | max n role filler ih =>
    apply not_congr
    apply count_transport Sum.inl Sum.inl_injective
    · intro y
      exact and_congr Iff.rfl (ih y)
    · intro y edge
      cases y with
      | inl old => exact ⟨old, rfl⟩
      | inr fresh => exact False.elim edge.1

/-- Exact truth at an isolated point; no cardinality is capped or enumerated. -/
def shell {Class Role : Type} : Concept Class Role → Prop
  | .top => True
  | .bottom | .atom _ | .some _ _ | .self _ => False
  | .neg inner => ¬shell inner
  | .and left right => shell left ∧ shell right
  | .or left right => shell left ∨ shell right
  | .all _ _ | .max _ _ _ => True
  | .min n _ _ => n = 0

theorem count_empty {Object : Type} (predicate : Object → Prop)
    (empty : ∀ x, ¬predicate x) (n : Nat) : count predicate n ↔ n = 0 := by
  cases n with
  | zero =>
    constructor
    · intro _; rfl
    · intro _
      exact ⟨fun i => Fin.elim0 i, fun i _ _ => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n =>
    constructor
    · rintro ⟨witnesses, _, matched⟩
      exact False.elim (empty (witnesses 0) (matched 0))
    · intro impossible
      exact False.elim (Nat.succ_ne_zero n impossible)

theorem fresh_concepts_shell {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (concept : Concept Class Role) (fresh : Fresh) :
    holds (extend model) concept (.inr fresh) ↔ shell concept := by
  induction concept with
  | top | bottom | atom | self => rfl
  | neg inner ih => exact not_congr ih
  | and left right ihLeft ihRight => exact and_congr ihLeft ihRight
  | or left right ihLeft ihRight => exact or_congr ihLeft ihRight
  | some role filler _ => simp [holds, extend, shell]
  | all role filler _ => simp [holds, extend, shell]
  | min n role filler _ =>
    apply count_empty
    intro y matched
    simpa [extend] using matched.1
  | max n role filler _ =>
    change (¬count (fun y => (extend model).role role (.inr fresh) y ∧
      holds (extend model) filler y) (n + 1)) ↔ True
    have empty : ∀ y, ¬((extend model).role role (.inr fresh) y ∧
        holds (extend model) filler y) := by
      intro y matched
      simpa [extend] using matched.1
    rw [count_empty _ empty]
    simp

theorem inclusion_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (left right : Concept Class Role)
    (base : ∀ x, holds model left x → holds model right x)
    (shellValid : shell left → shell right) :
    ∀ x : Sum Object Fresh, holds (extend model) left x → holds (extend model) right x := by
  intro x matched
  cases x with
  | inl old =>
    exact (old_concepts_preserved model right old).mpr
      (base old ((old_concepts_preserved model left old).mp matched))
  | inr fresh =>
    exact (fresh_concepts_shell model right fresh).mpr
      (shellValid ((fresh_concepts_shell model left fresh).mp matched))

theorem role_inclusion_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (left right : Role)
    (base : ∀ x y, model.role left x y → model.role right x y) :
    ∀ x y : Sum Object Fresh, (extend model).role left x y → (extend model).role right x y := by
  intro x y edge
  cases x <;> cases y <;> simp_all [extend]

theorem transitivity_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (role : Role)
    (base : ∀ x y z, model.role role x y → model.role role y z → model.role role x z) :
    ∀ x y z : Sum Object Fresh, (extend model).role role x y →
      (extend model).role role y z → (extend model).role role x z := by
  intro x y z first second
  cases x <;> cases y <;> cases z <;> simp_all [extend]
  all_goals exact base _ _ _ first second

theorem functionality_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (role : Role)
    (base : ∀ x y z, model.role role x y → model.role role x z → y = z) :
    ∀ x y z : Sum Object Fresh, (extend model).role role x y →
      (extend model).role role x z → y = z := by
  intro x y z first second
  cases x <;> cases y <;> cases z <;> simp_all [extend]
  all_goals exact base _ _ _ first second

theorem inverse_functionality_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (role : Role)
    (base : ∀ x y z, model.role role x z → model.role role y z → x = y) :
    ∀ x y z : Sum Object Fresh, (extend model).role role x z →
      (extend model).role role y z → x = y := by
  intro x y z first second
  cases x <;> cases y <;> cases z <;> simp_all [extend]
  all_goals exact base _ _ _ first second

theorem inverse_roles_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (left right : Role)
    (base : ∀ x y, model.role left x y ↔ model.role right y x) :
    ∀ x y : Sum Object Fresh, (extend model).role left x y ↔ (extend model).role right y x := by
  intro x y
  cases x <;> cases y <;> simp_all [extend]

theorem named_subsumption_preserved {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (left right : Class) :
    (∀ x : Sum Object Fresh, (extend model).concept left x → (extend model).concept right x) ↔
      (∀ x, model.concept left x → model.concept right x) := by
  constructor
  · intro entailed old matched
    exact entailed (.inl old) matched
  · intro entailed x matched
    cases x with
    | inl old => exact entailed old matched
    | inr fresh => exact False.elim matched

theorem named_satisfiability_preserved {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (name : Class) :
    (∃ x : Sum Object Fresh, (extend model).concept name x) ↔
      (∃ x, model.concept name x) := by
  constructor
  · rintro ⟨x, matched⟩
    cases x with
    | inl old => exact ⟨old, matched⟩
    | inr fresh => exact False.elim matched
  · rintro ⟨old, matched⟩
    exact ⟨.inl old, matched⟩

theorem symmetry_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (role : Role)
    (base : ∀ x y, model.role role x y → model.role role y x) :
    ∀ x y : Sum Object Fresh, (extend model).role role x y → (extend model).role role y x := by
  intro x y edge
  cases x with
  | inl old =>
    cases y with
    | inl target => exact base old target edge
    | inr fresh => exact False.elim edge
  | inr fresh => exact False.elim edge

theorem asymmetry_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (role : Role)
    (base : ∀ x y, model.role role x y → ¬model.role role y x) :
    ∀ x y : Sum Object Fresh, (extend model).role role x y → ¬(extend model).role role y x := by
  intro x y edge
  cases x with
  | inl old =>
    cases y with
    | inl target => exact base old target edge
    | inr fresh => exact False.elim edge
  | inr fresh => exact False.elim edge

theorem irreflexivity_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (role : Role)
    (base : ∀ x, ¬model.role role x x) :
    ∀ x : Sum Object Fresh, ¬(extend model).role role x x := by
  intro x
  cases x with
  | inl old => exact base old
  | inr fresh => exact id

theorem disjoint_roles_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (left right : Role)
    (base : ∀ x y, model.role left x y → ¬model.role right x y) :
    ∀ x y : Sum Object Fresh, (extend model).role left x y → ¬(extend model).role right x y := by
  intro x y edge
  cases x with
  | inl old =>
    cases y with
    | inl target => exact base old target edge
    | inr fresh => exact False.elim edge
  | inr fresh => exact False.elim edge

def path {Class Role Object : Type} (model : Model Class Role Object)
    : List Role → Object → Object → Prop
  | [], x, y => x = y
  | role :: tail, x, y => ∃ middle, model.role role x middle ∧ path model tail middle y

theorem path_from_old {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (roles : List Role) (old : Object)
    (target : Sum Object Fresh) :
    path (extend model) roles (.inl old) target ↔
      ∃ y, target = .inl y ∧ path model roles old y := by
  induction roles generalizing old target with
  | nil =>
    constructor
    · intro equal
      exact ⟨old, equal.symm, rfl⟩
    · rintro ⟨y, equal, matched⟩
      exact matched ▸ equal.symm
  | cons role tail ih =>
    constructor
    · rintro ⟨middle, edge, matched⟩
      cases middle with
      | inl previous =>
        obtain ⟨y, equal, remainder⟩ := (ih previous target).mp matched
        exact ⟨y, equal, previous, edge, remainder⟩
      | inr fresh => exact False.elim edge
    · rintro ⟨y, equal, middle, edge, matched⟩
      exact ⟨.inl middle, edge, (ih middle target).mpr ⟨y, equal, matched⟩⟩

theorem chain_extended {Class Role Object Fresh : Type}
    (model : Model Class Role Object) (roles : List Role) (result : Role)
    (nonempty : roles ≠ [])
    (base : ∀ x y, path model roles x y → model.role result x y) :
    ∀ x y : Sum Object Fresh, path (extend model) roles x y → (extend model).role result x y := by
  intro x y matched
  cases x with
  | inl old =>
    obtain ⟨target, equal, original⟩ := (path_from_old model roles old y).mp matched
    subst y
    exact base old target original
  | inr fresh =>
    cases roles with
    | nil => exact False.elim (nonempty rfl)
    | cons role tail =>
      obtain ⟨middle, edge, _⟩ := matched
      exact False.elim edge

def usesRole {Class Role : Type} : Concept Class Role → Role → Prop
  | .top, _ | .bottom, _ | .atom _, _ => False
  | .neg inner, role => usesRole inner role
  | .and left right, role | .or left right, role => usesRole left role ∨ usesRole right role
  | .some role filler, query | .all role filler, query
  | .min _ role filler, query | .max _ role filler, query => query = role ∨ usesRole filler query
  | .self role, query => query = role

theorem count_congr {Object : Type} (left right : Object → Prop)
    (agree : ∀ x, left x ↔ right x) (n : Nat) : count left n ↔ count right n := by
  constructor
  · rintro ⟨witnesses, distinct, matched⟩
    exact ⟨witnesses, distinct, fun i => (agree _).mp (matched i)⟩
  · rintro ⟨witnesses, distinct, matched⟩
    exact ⟨witnesses, distinct, fun i => (agree _).mpr (matched i)⟩

theorem role_locality {Class Role Object : Type}
    (left right : Model Class Role Object) (concept : Concept Class Role)
    (classes : ∀ name x, left.concept name x ↔ right.concept name x)
    (roles : ∀ role, usesRole concept role → ∀ x y, left.role role x y ↔ right.role role x y)
    (x : Object) : holds left concept x ↔ holds right concept x := by
  induction concept generalizing x with
  | top | bottom => rfl
  | atom name => exact classes name x
  | neg inner ih => exact not_congr (ih roles x)
  | and first second ihFirst ihSecond =>
    exact and_congr (ihFirst (fun role used => roles role (Or.inl used)) x)
      (ihSecond (fun role used => roles role (Or.inr used)) x)
  | or first second ihFirst ihSecond =>
    exact or_congr (ihFirst (fun role used => roles role (Or.inl used)) x)
      (ihSecond (fun role used => roles role (Or.inr used)) x)
  | some role filler ih =>
    have edge := roles role (Or.inl rfl) x
    have matched := fun y => ih (fun r used => roles r (Or.inr used)) y
    exact exists_congr (fun y => and_congr (edge y) (matched y))
  | all role filler ih =>
    have edge := roles role (Or.inl rfl) x
    have matched := fun y => ih (fun r used => roles r (Or.inr used)) y
    exact forall_congr' (fun y => imp_congr (edge y) (matched y))
  | min n role filler ih =>
    apply count_congr
    intro y
    exact and_congr (roles role (Or.inl rfl) x y)
      (ih (fun r used => roles r (Or.inr used)) y)
  | max n role filler ih =>
    apply not_congr
    apply count_congr
    intro y
    exact and_congr (roles role (Or.inl rfl) x y)
      (ih (fun r used => roles r (Or.inr used)) y)
  | self role => exact roles role rfl x x

def addInertFacts {Class Role Object : Type} (model : Model Class Role Object)
    (inert : Role → Prop) (facts : Role → Object → Object → Prop) : Model Class Role Object where
  concept := model.concept
  role := fun role x y => model.role role x y ∨ (inert role ∧ facts role x y)

theorem inert_fact_satisfied {Class Role Object : Type} (model : Model Class Role Object)
    (inert : Role → Prop) (facts : Role → Object → Object → Prop)
    (role : Role) (x y : Object) (unused : inert role) (asserted : facts role x y) :
    (addInertFacts model inert facts).role role x y := Or.inr ⟨unused, asserted⟩

theorem inert_facts_preserve_concepts {Class Role Object : Type}
    (model : Model Class Role Object) (inert : Role → Prop)
    (facts : Role → Object → Object → Prop) (concept : Concept Class Role)
    (unused : ∀ role, usesRole concept role → ¬inert role) (x : Object) :
    holds (addInertFacts model inert facts) concept x ↔ holds model concept x := by
  apply role_locality
  · intro name y; rfl
  · intro role used y z
    change (model.role role y z ∨ (inert role ∧ facts role y z)) ↔ model.role role y z
    simp [unused role used]

#print axioms count_congr
#print axioms role_locality
#print axioms inert_fact_satisfied
#print axioms inert_facts_preserve_concepts
#print axioms symmetry_extended
#print axioms asymmetry_extended
#print axioms irreflexivity_extended
#print axioms disjoint_roles_extended
#print axioms path_from_old
#print axioms chain_extended
#print axioms role_inclusion_extended
#print axioms transitivity_extended
#print axioms functionality_extended
#print axioms inverse_functionality_extended
#print axioms inverse_roles_extended
#print axioms named_subsumption_preserved
#print axioms named_satisfiability_preserved
#print axioms count_empty
#print axioms fresh_concepts_shell
#print axioms inclusion_extended
#print axioms count_transport
#print axioms old_concepts_preserved
end ContextCalculus.IsolatedObjectModelExtension
