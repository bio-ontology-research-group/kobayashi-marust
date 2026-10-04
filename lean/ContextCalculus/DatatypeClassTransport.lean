import ContextCalculus.FunctionalDatatypeQuotient

/-! Class-expression transport for a checked datatype reduction. The `dataAtom`
indices stand for complete datatype restrictions (including cardinalities), not
individual range names. Their pointwise equivalence must be proved separately.
This file does not certify parsing or generation of numeric profiles. -/
namespace ContextCalculus.DatatypeClassTransport
universe u v w z

inductive Expr (Class : Type u) (Role : Type v) (Data : Type w) where
  | atom : Class → Expr Class Role Data
  | dataAtom : Data → Expr Class Role Data
  | neg : Expr Class Role Data → Expr Class Role Data
  | conj : Expr Class Role Data → Expr Class Role Data → Expr Class Role Data
  | disj : Expr Class Role Data → Expr Class Role Data → Expr Class Role Data
  | some : Role → Expr Class Role Data → Expr Class Role Data
  | all : Role → Expr Class Role Data → Expr Class Role Data
  | min : Role → Nat → Expr Class Role Data → Expr Class Role Data
  | max : Role → Nat → Expr Class Role Data → Expr Class Role Data

open FunctionalDatatypeQuotient (atLeast)

def holds {Class : Type u} {Role : Type v} {Data : Type w} {O : Type z}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (data : Data → O → Prop) : Expr Class Role Data → O → Prop
  | .atom c, x => classes c x
  | .dataAtom d, x => data d x
  | .neg p, x => ¬ holds classes roles data p x
  | .conj p q, x => holds classes roles data p x ∧ holds classes roles data q x
  | .disj p q, x => holds classes roles data p x ∨ holds classes roles data q x
  | .some r p, x => ∃ y, roles r x y ∧ holds classes roles data p y
  | .all r p, x => ∀ y, roles r x y → holds classes roles data p y
  | .min r n p, x => atLeast (roles r) (holds classes roles data p) x n
  | .max r n p, x => ¬ atLeast (roles r) (holds classes roles data p) x (n+1)

theorem atLeast_congr {O : Type z} (r : O → O → Prop)
    (p q : O → Prop) (equal : ∀ y, p y ↔ q y) (x : O) (n : Nat) :
    atLeast r p x n ↔ atLeast r q x n := by
  constructor
  · rintro ⟨vs, edges, distinct⟩
    exact ⟨vs, fun i => ⟨(edges i).1, (equal (vs i)).mp (edges i).2⟩, distinct⟩
  · rintro ⟨vs, edges, distinct⟩
    exact ⟨vs, fun i => ⟨(edges i).1, (equal (vs i)).mpr (edges i).2⟩, distinct⟩

/-- Object structure and atomic classes are unchanged by the numeric quotient.
Every checked datatype restriction can therefore be replaced under arbitrary
Boolean/object-quantifier nesting, including qualified object cardinality. -/
theorem class_preserved {Class : Type u} {Role : Type v} {Data : Type w} {O : Type z}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (before after : Data → O → Prop) (equal : ∀ d x, before d x ↔ after d x)
    (e : Expr Class Role Data) :
    ∀ x, holds classes roles before e x ↔ holds classes roles after e x := by
  induction e with
  | atom c => intro x; exact Iff.rfl
  | dataAtom d => exact equal d
  | neg p ih => intro x; exact not_congr (ih x)
  | conj p q ihp ihq => intro x; exact and_congr (ihp x) (ihq x)
  | disj p q ihp ihq => intro x; exact or_congr (ihp x) (ihq x)
  | some r p ih =>
      intro x
      exact exists_congr (fun y => and_congr Iff.rfl (ih y))
  | all r p ih =>
      intro x
      exact forall_congr' (fun y => imp_congr Iff.rfl (ih y))
  | min r n p ih => intro x; exact atLeast_congr (roles r) _ _ ih x n
  | max r n p ih => intro x; exact not_congr (atLeast_congr (roles r) _ _ ih x (n+1))

/-- A list of GCIs is preserved, not just the individual concept tests. -/
theorem tbox_preserved {Class : Type u} {Role : Type v} {Data : Type w} {O : Type z}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (before after : Data → O → Prop) (equal : ∀ d x, before d x ↔ after d x)
    (axioms : List (Expr Class Role Data × Expr Class Role Data)) :
    (∀ ax ∈ axioms, ∀ x, holds classes roles before ax.1 x → holds classes roles before ax.2 x) ↔
    (∀ ax ∈ axioms, ∀ x, holds classes roles after ax.1 x → holds classes roles after ax.2 x) := by
  apply forall_congr'
  intro ax
  apply imp_congr Iff.rfl
  apply forall_congr'
  intro x
  exact imp_congr (class_preserved classes roles before after equal ax.1 x)
    (class_preserved classes roles before after equal ax.2 x)

/-- Preserve positive or negated class assertions on the unchanged object
carrier. Negation is already a constructor of the transported expression. -/
theorem abox_preserved {Class : Type u} {Role : Type v} {Data : Type w} {O : Type z}
    (classes : Class → O → Prop) (roles : Role → O → O → Prop)
    (before after : Data → O → Prop) (equal : ∀ d x, before d x ↔ after d x)
    (assertions : List (Expr Class Role Data × O)) :
    (∀ ax ∈ assertions, holds classes roles before ax.1 ax.2) ↔
    (∀ ax ∈ assertions, holds classes roles after ax.1 ax.2) := by
  apply forall_congr'
  intro ax
  exact imp_congr Iff.rfl (class_preserved classes roles before after equal ax.1 ax.2)

#print axioms abox_preserved
#print axioms atLeast_congr
#print axioms class_preserved
#print axioms tbox_preserved
end ContextCalculus.DatatypeClassTransport
