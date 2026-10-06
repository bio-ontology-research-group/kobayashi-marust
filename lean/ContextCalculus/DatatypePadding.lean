import ContextCalculus.DatatypeClassTransport

/-! The forward carrier-extension obligation for a datatype padding witness.
This module does not certify a Rust witness search, reverse model transport,
or admission of any additional ontology. Data restrictions are abstract atoms;
their interpretation at object and padding nodes remains an explicit premise.
-/
namespace ContextCalculus.DatatypePadding

open DatatypeClassTransport (Expr holds)
open FunctionalDatatypeQuotient (atLeast)

universe u v w z t

def extend {O : Type z} {V : Type t} (object : O → Prop) (padding : V → Prop) :
    Sum O V → Prop
  | .inl x => object x
  | .inr y => padding y

def objectRole {O : Type z} {V : Type t} (role : O → O → Prop) :
    Sum O V → Sum O V → Prop
  | .inl x, .inl y => role x y
  | _, _ => False

theorem minimum_on_objects {O : Type z} {V : Type t}
    (role : O → O → Prop) (p : O → Prop) (q : Sum O V → Prop)
    (agree : ∀ x, p x ↔ q (.inl x)) (x : O) (n : Nat) :
    atLeast role p x n ↔ atLeast (objectRole role) q (.inl x) n := by
  constructor
  · rintro ⟨vs, edges, distinct⟩
    refine ⟨fun i => .inl (vs i), ?_, ?_⟩
    · intro i
      exact ⟨(edges i).1, (agree (vs i)).mp (edges i).2⟩
    · intro i j equal
      exact distinct i j (Sum.inl.inj equal)
  · rintro ⟨ws, edges, distinct⟩
    let vs : Fin n → O := fun i => match ws i with
      | .inl y => y
      | .inr _ => x
    have mapped : ∀ i, ws i = Sum.inl (vs i) := by
      intro i
      cases h : ws i with
      | inl y => simp [vs, h]
      | inr y =>
          have edge := (edges i).1
          rw [h] at edge
          exact False.elim edge
    refine ⟨vs, ?_, ?_⟩
    · intro i
      have edge := edges i
      rw [mapped i] at edge
      exact ⟨edge.1, (agree (vs i)).mpr edge.2⟩
    · intro i j equal
      apply distinct i j
      exact (mapped i).trans ((congrArg Sum.inl equal).trans (mapped j).symm)

theorem minimum_on_padding {O : Type z} {V : Type t}
    (role : O → O → Prop) (q : Sum O V → Prop) (y : V) (n : Nat) :
    atLeast (objectRole role) q (.inr y) n ↔ n = 0 := by
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

def paddingHolds {Class : Type u} {Role : Type v} {Data : Type w}
    (classes : Class → Prop) (data : Data → Prop) : Expr Class Role Data → Prop
  | .atom c => classes c
  | .dataAtom d => data d
  | .neg p => ¬ paddingHolds classes data p
  | .conj p q => paddingHolds classes data p ∧ paddingHolds classes data q
  | .disj p q => paddingHolds classes data p ∨ paddingHolds classes data q
  | .some _ _ => False
  | .all _ _ => True
  | .min _ n _ => n = 0
  | .max _ _ _ => True

theorem class_on_objects {Class : Type u} {Role : Type v} {Data : Type w}
    {O : Type z} {V : Type t}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (data : Data → O → Prop) (paddingClasses : Class → V → Prop)
    (paddingData : Data → V → Prop) (e : Expr Class Role Data) :
    ∀ x, holds classes roles data e x ↔
      holds (fun c => extend (classes c) (paddingClasses c))
        (fun r => objectRole (roles r))
        (fun d => extend (data d) (paddingData d)) e (.inl x) := by
  induction e with
  | atom c => intro x; rfl
  | dataAtom d => intro x; rfl
  | neg p ih => intro x; exact not_congr (ih x)
  | conj p q ihp ihq => intro x; exact and_congr (ihp x) (ihq x)
  | disj p q ihp ihq => intro x; exact or_congr (ihp x) (ihq x)
  | some r p ih =>
      intro x
      constructor
      · rintro ⟨y, edge, hp⟩
        exact ⟨.inl y, edge, (ih y).mp hp⟩
      · rintro ⟨y, edge, hp⟩
        cases y with
        | inl y => exact ⟨y, edge, (ih y).mpr hp⟩
        | inr y => exact False.elim edge
  | all r p ih =>
      intro x
      constructor
      · intro universal y edge
        cases y with
        | inl y => exact (ih y).mp (universal y edge)
        | inr y => exact False.elim edge
      · intro universal y edge
        exact (ih y).mpr (universal (.inl y) edge)
  | min r n p ih => intro x; exact minimum_on_objects (roles r) _ _ ih x n
  | max r n p ih =>
      intro x
      exact not_congr (minimum_on_objects (roles r) _ _ ih x (n+1))

theorem class_on_padding {Class : Type u} {Role : Type v} {Data : Type w}
    {O : Type z} {V : Type t}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (data : Data → O → Prop) (paddingClasses : Class → V → Prop)
    (paddingData : Data → V → Prop) (e : Expr Class Role Data) :
    ∀ y, holds (fun c => extend (classes c) (paddingClasses c))
      (fun r => objectRole (roles r))
      (fun d => extend (data d) (paddingData d)) e (.inr y) ↔
      paddingHolds (fun c => paddingClasses c y) (fun d => paddingData d y) e := by
  induction e with
  | atom c => intro y; rfl
  | dataAtom d => intro y; rfl
  | neg p ih => intro y; exact not_congr (ih y)
  | conj p q ihp ihq => intro y; exact and_congr (ihp y) (ihq y)
  | disj p q ihp ihq => intro y; exact or_congr (ihp y) (ihq y)
  | some r p => intro y; simp [holds, objectRole, paddingHolds]
  | all r p => intro y; simp [holds, objectRole, paddingHolds]
  | min r n p => intro y; exact minimum_on_padding (roles r) _ y n
  | max r n p =>
      intro y
      simp only [holds, paddingHolds]
      rw [minimum_on_padding]
      simp

/-- A checked padding type must satisfy every GCI, including those involving
data restrictions. Checking only non-datatype axioms would not establish this
theorem's right-hand premise. Object/data role typing and the concrete meaning
of each data atom are not inferred by this theorem. -/
theorem tbox_extension_iff {Class : Type u} {Role : Type v} {Data : Type w}
    {O : Type z} {V : Type t}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (data : Data → O → Prop) (paddingClasses : Class → V → Prop)
    (paddingData : Data → V → Prop)
    (axioms : List (Expr Class Role Data × Expr Class Role Data)) :
    (∀ ax ∈ axioms, ∀ node,
      holds (fun c => extend (classes c) (paddingClasses c))
        (fun r => objectRole (roles r))
        (fun d => extend (data d) (paddingData d)) ax.1 node →
      holds (fun c => extend (classes c) (paddingClasses c))
        (fun r => objectRole (roles r))
        (fun d => extend (data d) (paddingData d)) ax.2 node) ↔
    ((∀ ax ∈ axioms, ∀ x, holds classes roles data ax.1 x → holds classes roles data ax.2 x) ∧
     (∀ ax ∈ axioms, ∀ y,
       paddingHolds (fun c => paddingClasses c y) (fun d => paddingData d y) ax.1 →
       paddingHolds (fun c => paddingClasses c y) (fun d => paddingData d y) ax.2)) := by
  constructor
  · intro model
    constructor
    · intro ax member x premise
      exact (class_on_objects classes roles data paddingClasses paddingData ax.2 x).mpr
        (model ax member (.inl x)
          ((class_on_objects classes roles data paddingClasses paddingData ax.1 x).mp premise))
    · intro ax member y premise
      exact (class_on_padding classes roles data paddingClasses paddingData ax.2 y).mp
        (model ax member (.inr y)
          ((class_on_padding classes roles data paddingClasses paddingData ax.1 y).mpr premise))
  · rintro ⟨objects, padding⟩ ax member node premise
    cases node with
    | inl x =>
        exact (class_on_objects classes roles data paddingClasses paddingData ax.2 x).mp
          (objects ax member x
            ((class_on_objects classes roles data paddingClasses paddingData ax.1 x).mpr premise))
    | inr y =>
        exact (class_on_padding classes roles data paddingClasses paddingData ax.2 y).mpr
          (padding ax member y
            ((class_on_padding classes roles data paddingClasses paddingData ax.1 y).mp premise))

#print axioms minimum_on_objects
#print axioms minimum_on_padding
#print axioms class_on_objects
#print axioms class_on_padding
#print axioms tbox_extension_iff

end ContextCalculus.DatatypePadding
