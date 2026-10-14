import ContextCalculus.DatatypePaddingCheck

/-! Source-expression semantics for the diagnostic padding checker. Unlike the
lowered expression language, this retains top, bottom, nominal and self nodes.
The lowering theorem is local to an edgeless padding point, not an equivalence
on original objects. JSON decoding, Rust agreement and datatype value binding
remain separate obligations. -/
namespace ContextCalculus.DatatypePadding

open DatatypeClassTransport (Expr)
open FunctionalDatatypeQuotient (atLeast)

inductive SourceExpr (Class Role Individual : Type) where
  | top
  | bottom
  | name : Class → SourceExpr Class Role Individual
  | nominal : Individual → SourceExpr Class Role Individual
  | neg : SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | conj : SourceExpr Class Role Individual → SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | disj : SourceExpr Class Role Individual → SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | some : Role → SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | all : Role → SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | min : Role → Nat → SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | max : Role → Nat → SourceExpr Class Role Individual → SourceExpr Class Role Individual
  | self : Role → SourceExpr Class Role Individual

def SourceExpr.holds {Class Role Individual Domain : Type}
    (classes : Class → Domain → Prop) (roles : Role → Domain → Domain → Prop)
    (nominals : Individual → Domain) : SourceExpr Class Role Individual → Domain → Prop
  | .top, _ => True
  | .bottom, _ => False
  | .name c, x => classes c x
  | .nominal i, x => x = nominals i
  | .neg e, x => ¬ e.holds classes roles nominals x
  | .conj p q, x => p.holds classes roles nominals x ∧ q.holds classes roles nominals x
  | .disj p q, x => p.holds classes roles nominals x ∨ q.holds classes roles nominals x
  | .some r p, x => ∃ y, roles r x y ∧ p.holds classes roles nominals y
  | .all r p, x => ∀ y, roles r x y → p.holds classes roles nominals y
  | .min r n p, x => atLeast (roles r) (p.holds classes roles nominals) x n
  | .max r n p, x => ¬ atLeast (roles r) (p.holds classes roles nominals) x (n+1)
  | .self r, x => roles r x x

def SourceExpr.lower {Class Role Individual : Type} :
    SourceExpr Class Role Individual → Expr Class Role Bool
  | .top => .dataAtom true
  | .bottom => .dataAtom false
  | .name c => .atom c
  | .nominal _ => .dataAtom false
  | .neg p => .neg p.lower
  | .conj p q => .conj p.lower q.lower
  | .disj p q => .disj p.lower q.lower
  | .some r p => .some r p.lower
  | .all r p => .all r p.lower
  | .min r n p => .min r n p.lower
  | .max r n p => .max r n p.lower
  | .self r => .some r (.dataAtom true)

/-- Only names evaluated at the current point. Fillers are not evaluated at an
edgeless point, so their datatype names must not be forced to the witness's
ordinary-class valuation. -/
def SourceExpr.surfaceClasses {Class Role Individual : Type} :
    SourceExpr Class Role Individual → List Class
  | .name c => [c]
  | .neg p => p.surfaceClasses
  | .conj p q | .disj p q => p.surfaceClasses ++ q.surfaceClasses
  | _ => []

theorem atLeast_edgeless {Domain : Type} (role : Domain → Domain → Prop)
    (p : Domain → Prop) (x : Domain) (empty : ∀ y, ¬ role x y) (n : Nat) :
    atLeast role p x n ↔ n = 0 := by
  cases n with
  | zero =>
      constructor
      · intro _; rfl
      · intro _
        exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n =>
      constructor
      · rintro ⟨_, edges, _⟩
        exact False.elim (empty _ (edges ⟨0, Nat.zero_lt_succ n⟩).1)
      · intro impossible
        exact False.elim (Nat.noConfusion impossible)

theorem SourceExpr.lower_padding_iff {Class Role Individual Domain : Type}
    (classes : Class → Domain → Prop) (roles : Role → Domain → Domain → Prop)
    (nominals : Individual → Domain) (padding : Class → Bool) (x : Domain)
    (e : SourceExpr Class Role Individual)
    (classAgreement : ∀ c ∈ e.surfaceClasses, classes c x ↔ padding c = true)
    (noNominals : ∀ i, x ≠ nominals i)
    (noOutgoing : ∀ r y, ¬ roles r x y) :
    paddingHolds (fun c => padding c = true) (fun b => b = true) e.lower ↔
      e.holds classes roles nominals x := by
  induction e with
  | top => simp [lower, paddingHolds, holds]
  | bottom => simp [lower, paddingHolds, holds]
  | name c => exact (classAgreement c (by simp [surfaceClasses])).symm
  | nominal i => simp [lower, paddingHolds, holds, noNominals i]
  | neg p ih => exact not_congr (ih classAgreement)
  | conj p q ihp ihq =>
      exact and_congr
        (ihp (fun c member => classAgreement c (by simp [surfaceClasses, member])))
        (ihq (fun c member => classAgreement c (by simp [surfaceClasses, member])))
  | disj p q ihp ihq =>
      exact or_congr
        (ihp (fun c member => classAgreement c (by simp [surfaceClasses, member])))
        (ihq (fun c member => classAgreement c (by simp [surfaceClasses, member])))
  | some r p => simp [lower, paddingHolds, holds, noOutgoing]
  | all r p => simp [lower, paddingHolds, holds, noOutgoing]
  | min r n p =>
      exact (atLeast_edgeless (roles r) _ x (noOutgoing r) n).symm
  | max r n p =>
      simp [lower, paddingHolds, holds,
        atLeast_edgeless (roles r) _ x (noOutgoing r) (n+1)]
  | self r => simp [lower, paddingHolds, holds, noOutgoing]

theorem SourceExpr.eval_padding_iff {Class Role Individual Domain : Type}
    (classes : Class → Domain → Prop) (roles : Role → Domain → Domain → Prop)
    (nominals : Individual → Domain) (padding : Class → Bool) (x : Domain)
    (e : SourceExpr Class Role Individual)
    (classAgreement : ∀ c ∈ e.surfaceClasses, classes c x ↔ padding c = true)
    (noNominals : ∀ i, x ≠ nominals i)
    (noOutgoing : ∀ r y, ¬ roles r x y) :
    paddingEval padding id e.lower = true ↔ e.holds classes roles nominals x :=
  (paddingEval_iff padding id e.lower).trans
    (e.lower_padding_iff classes roles nominals padding x classAgreement noNominals noOutgoing)

inductive SourceAxiom (Class Role Individual : Type) where
  | subClass : SourceExpr Class Role Individual → SourceExpr Class Role Individual → SourceAxiom Class Role Individual
  | equivalent : SourceExpr Class Role Individual → SourceExpr Class Role Individual → SourceAxiom Class Role Individual
  | disjoint : SourceExpr Class Role Individual → SourceExpr Class Role Individual → SourceAxiom Class Role Individual

def SourceAxiom.lower {Class Role Individual : Type} :
    SourceAxiom Class Role Individual → List (Expr Class Role Bool × Expr Class Role Bool)
  | .subClass left right => [(left.lower, right.lower)]
  | .equivalent left right => [(left.lower, right.lower), (right.lower, left.lower)]
  | .disjoint left right => [(.conj left.lower right.lower, .dataAtom false)]

def SourceAxiom.holds {Class Role Individual Domain : Type}
    (classes : Class → Domain → Prop) (roles : Role → Domain → Domain → Prop)
    (nominals : Individual → Domain) (x : Domain) : SourceAxiom Class Role Individual → Prop
  | .subClass left right => left.holds classes roles nominals x → right.holds classes roles nominals x
  | .equivalent left right => left.holds classes roles nominals x ↔ right.holds classes roles nominals x
  | .disjoint left right => ¬ (left.holds classes roles nominals x ∧ right.holds classes roles nominals x)

def SourceAxiom.surfaceClasses {Class Role Individual : Type} :
    SourceAxiom Class Role Individual → List Class
  | .subClass left right | .equivalent left right | .disjoint left right =>
      left.surfaceClasses ++ right.surfaceClasses

theorem SourceAxiom.check_padding_iff {Class Role Individual Domain : Type}
    (classes : Class → Domain → Prop) (roles : Role → Domain → Domain → Prop)
    (nominals : Individual → Domain) (padding : Class → Bool) (x : Domain)
    (ax : SourceAxiom Class Role Individual)
    (classAgreement : ∀ c ∈ ax.surfaceClasses, classes c x ↔ padding c = true)
    (noNominals : ∀ i, x ≠ nominals i)
    (noOutgoing : ∀ r y, ¬ roles r x y) :
    checkPadding padding id ax.lower = true ↔ ax.holds classes roles nominals x := by
  rw [checkPadding_iff]
  cases ax with
  | subClass left right | equivalent left right | disjoint left right =>
      have lhs := left.lower_padding_iff classes roles nominals padding x
        (fun c member => classAgreement c (by simp [surfaceClasses, member])) noNominals noOutgoing
      have rhs := right.lower_padding_iff classes roles nominals padding x
        (fun c member => classAgreement c (by simp [surfaceClasses, member])) noNominals noOutgoing
      simp [lower, holds, paddingHolds, lhs, rhs, iff_def]

def checkSourcePadding {Class Role Individual : Type} (padding : Class → Bool)
    (axioms : List (SourceAxiom Class Role Individual)) : Bool :=
  axioms.all fun ax => checkPadding padding id ax.lower

theorem checkSourcePadding_iff {Class Role Individual Domain : Type}
    (classes : Class → Domain → Prop) (roles : Role → Domain → Domain → Prop)
    (nominals : Individual → Domain) (padding : Class → Bool) (x : Domain)
    (axioms : List (SourceAxiom Class Role Individual))
    (classAgreement : ∀ ax ∈ axioms, ∀ c ∈ ax.surfaceClasses, classes c x ↔ padding c = true)
    (noNominals : ∀ i, x ≠ nominals i)
    (noOutgoing : ∀ r y, ¬ roles r x y) :
    checkSourcePadding padding axioms = true ↔
      ∀ ax ∈ axioms, ax.holds classes roles nominals x := by
  simp only [checkSourcePadding, List.all_eq_true]
  apply forall_congr'
  intro ax
  constructor
  · intro accepted member
    exact (ax.check_padding_iff classes roles nominals padding x
      (classAgreement ax member) noNominals noOutgoing).mp (accepted member)
  · intro accepted member
    exact (ax.check_padding_iff classes roles nominals padding x
      (classAgreement ax member) noNominals noOutgoing).mpr (accepted member)

#print axioms atLeast_edgeless
#print axioms SourceExpr.lower_padding_iff
#print axioms SourceExpr.eval_padding_iff
#print axioms SourceAxiom.check_padding_iff
#print axioms checkSourcePadding_iff

end ContextCalculus.DatatypePadding
