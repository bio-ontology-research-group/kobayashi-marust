import ContextCalculus.FunctionalGroundDataProjection

/-! Semantic core of exact finite-value data elimination. Object individuals
and data values have independent types. This module does not certify lexical
parsing, fresh-name allocation, or the source admission implementation. -/
namespace ContextCalculus.FiniteDataMembership

inductive Expr (C R P D N : Type) where
  | atom : C → Expr C R P D N
  | value : P → D → Expr C R P D N
  | top : Expr C R P D N
  | bottom : Expr C R P D N
  | neg : Expr C R P D N → Expr C R P D N
  | conj : Expr C R P D N → Expr C R P D N → Expr C R P D N
  | disj : Expr C R P D N → Expr C R P D N → Expr C R P D N
  | some : R → Expr C R P D N → Expr C R P D N
  | all : R → Expr C R P D N → Expr C R P D N
  | min : Nat → R → Expr C R P D N → Expr C R P D N
  | max : Nat → R → Expr C R P D N → Expr C R P D N
  | nominal : N → Expr C R P D N
  | self : R → Expr C R P D N

variable {C R P D N O : Type}

def atLeast (n : Nat) (s : O → Prop) : Prop :=
  ∃ f : Fin n → O, (∀ i j, f i = f j → i = j) ∧ ∀ i, s (f i)

def eval (classes : C → O → Prop) (roles : R → O → O → Prop)
    (data : P → O → D → Prop) (names : N → O) : Expr C R P D N → O → Prop
  | .atom c, x => classes c x
  | .value p v, x => data p x v
  | .top, _ => True
  | .bottom, _ => False
  | .neg e, x => ¬ eval classes roles data names e x
  | .conj a b, x => eval classes roles data names a x ∧ eval classes roles data names b x
  | .disj a b, x => eval classes roles data names a x ∨ eval classes roles data names b x
  | .some r e, x => ∃ y, roles r x y ∧ eval classes roles data names e y
  | .all r e, x => ∀ y, roles r x y → eval classes roles data names e y
  | .min n r e, x => atLeast n (fun y => roles r x y ∧ eval classes roles data names e y)
  | .max n r e, x => ¬ atLeast (n+1) (fun y => roles r x y ∧ eval classes roles data names e y)
  | .nominal i, x => x = names i
  | .self r, x => roles r x x

/-- Every data demand names a value in the finite translated signature. -/
def supported (active : D → Prop) : Expr C R P D N → Prop
  | .value _ v => active v
  | .neg e | .some _ e | .all _ e | .min _ _ e | .max _ _ e => supported active e
  | .conj a b | .disj a b => supported active a ∧ supported active b
  | _ => True

/-- Fresh predicates use a disjoint signature summand. No data value is an
object node, and no unique-name assumption is made about source individuals. -/
def translate : Expr C R P D N → Expr (Sum C (P × D)) R P D N
  | .atom c => .atom (.inl c)
  | .value p v => .atom (.inr (p,v))
  | .top => .top
  | .bottom => .bottom
  | .neg e => .neg (translate e)
  | .conj a b => .conj (translate a) (translate b)
  | .disj a b => .disj (translate a) (translate b)
  | .some r e => .some r (translate e)
  | .all r e => .all r (translate e)
  | .min n r e => .min n r (translate e)
  | .max n r e => .max n r (translate e)
  | .nominal i => .nominal i
  | .self r => .self r

def extendedClasses (classes : C → O → Prop) (membership : P → D → O → Prop) :
    Sum C (P × D) → O → Prop
  | .inl c => classes c
  | .inr pv => membership pv.1 pv.2

def edge (active : D → Prop) (membership : P → D → O → Prop)
    (p : P) (x : O) (v : D) : Prop := active v ∧ membership p v x

theorem translation_exact (classes : C → O → Prop) (roles : R → O → O → Prop)
    (data : P → O → D → Prop) (names : N → O)
    (membership : P → D → O → Prop) (active : D → Prop)
    (represented : ∀ p v x, active v → (data p x v ↔ membership p v x))
    (e : Expr C R P D N) (admitted : supported active e) (x : O) :
    eval classes roles data names e x ↔
      eval (extendedClasses classes membership) roles data names (translate e) x := by
  induction e generalizing x with
  | value p v => exact represented p v x admitted
  | atom c => rfl
  | top => rfl
  | bottom => rfl
  | nominal i => rfl
  | self r => rfl
  | neg e ih => exact not_congr (ih admitted x)
  | conj a b ia ib => exact and_congr (ia admitted.1 x) (ib admitted.2 x)
  | disj a b ia ib => exact or_congr (ia admitted.1 x) (ib admitted.2 x)
  | some r e ih => simp only [eval, translate, ih admitted]
  | all r e ih => simp only [eval, translate, ih admitted]
  | min n r e ih => simp only [eval, translate, atLeast, ih admitted]
  | max n r e ih => simp only [eval, translate, atLeast, ih admitted]

theorem extension_translation_exact
    (classes : C → O → Prop) (roles : R → O → O → Prop) (names : N → O)
    (membership : P → D → O → Prop) (active : D → Prop)
    (e : Expr C R P D N) (admitted : supported active e) (x : O) :
    eval classes roles (edge active membership) names e x ↔
      eval (extendedClasses classes membership) roles (edge active membership)
        names (translate e) x := by
  apply translation_exact classes roles (edge active membership) names membership active
    (fun _ _ _ hv => ⟨And.right, fun hm => ⟨hv, hm⟩⟩) e admitted x

theorem extension_subproperty (active : D → Prop) (membership : P → D → O → Prop)
    (p q : P) (included : ∀ v x, active v → membership p v x → membership q v x)
    (x : O) (v : D) (source : edge active membership p x v) :
    edge active membership q x v := ⟨source.1, included v x source.1 source.2⟩

theorem extension_range (active : D → Prop) (membership : P → D → O → Prop)
    (range : P → D → Prop)
    (valid : ∀ p v x, active v → membership p v x → range p v)
    (p : P) (x : O) (v : D) (fact : edge active membership p x v) : range p v :=
  valid p v x fact.1 fact.2

theorem extension_domain (active : D → Prop) (membership : P → D → O → Prop)
    (domain : P → O → Prop)
    (valid : ∀ p v x, active v → membership p v x → domain p x)
    (p : P) (x : O) (v : D) (fact : edge active membership p x v) : domain p x :=
  valid p v x fact.1 fact.2

theorem extension_functional (active : D → Prop) (membership : P → D → O → Prop)
    (p : P) (compatible : ∀ v w x, active v → active w →
      membership p v x → membership p w x → v = w)
    (x : O) (v w : D) (left : edge active membership p x v)
    (right : edge active membership p x w) : v = w :=
  compatible v w x left.1 right.1 left.2 right.2


theorem extension_negative_iff (active : D → Prop) (membership : P → D → O → Prop)
    (p : P) (x : O) (v : D) (represented : active v) :
    (¬ edge active membership p x v) ↔ ¬ membership p v x := by
  simp only [edge, represented, true_and]

theorem extension_disjoint (active : D → Prop) (membership : P → D → O → Prop)
    (p q : P) (disjoint : ∀ v x, active v → ¬ (membership p v x ∧ membership q v x))
    (x : O) (v : D) : ¬ (edge active membership p x v ∧ edge active membership q x v) := by
  rintro ⟨left, right⟩
  exact disjoint v x left.1 ⟨left.2, right.2⟩

/-- Restricting any source data interpretation to represented values never
adds an edge and preserves every represented positive or negative demand. -/
theorem restriction_exact (active : D → Prop) (data : P → O → D → Prop)
    (p : P) (x : O) (v : D) (represented : active v) :
    edge active (fun q w y => data q y w) p x v ↔ data p x v := by
  simp only [edge, represented, true_and]


#print axioms translation_exact
#print axioms extension_translation_exact
#print axioms extension_functional
end ContextCalculus.FiniteDataMembership
