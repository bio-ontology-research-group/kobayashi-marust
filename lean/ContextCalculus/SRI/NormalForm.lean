import Mathlib.Logic.Basic

/-!
# The v1.6.3 normal form: ALC with inverse roles and role axioms

`docs/V1.6.3-HT-PLAN.md`. The OWL frontend of v1.6.3 translates every
ontology of the `SRI` part of `F` (`OWL.Ontology.isSRI`) into clauses of
this file, and the v1.6.3 reference procedure decides subsumption between
named concepts of these clauses.

Compared with the ALC normal form `Ctx.Clause`:

- a role in a clause is a role term, a role name or its inverse
  (`RoleT`), so `ObjectInverseOf` needs no extra clause kind;
- `∃R.d ⊑ c` is written `d ⊑ ∀R⁻.c` (`allRight d R.flip c`), so there is
  no `exLeft`;
- role axioms are role chains `R₁ ∘ … ∘ Rₙ ⊑ S` (`chain`). A role
  inclusion is a chain of length one, transitivity is `R ∘ R ⊑ R`,
  symmetry is `R ⊑ R⁻`, and inverse properties are two inclusions.

Regularity of the chains is not part of the normal form: the translation
is exact for any chains, and the decision procedure checks regularity
itself.
-/

namespace ContextCalculus.SRI

/-- A role term: a role name or the inverse of one. -/
inductive RoleT (Role : Type) where
  | pos (r : Role)
  | inv (r : Role)
deriving DecidableEq, Repr

/-- The inverse of a role term. -/
def RoleT.flip {Role : Type} : RoleT Role → RoleT Role
  | .pos r => .inv r
  | .inv r => .pos r

@[simp] theorem RoleT.flip_flip {Role : Type} (R : RoleT Role) : R.flip.flip = R := by
  cases R <;> rfl

/-- Normalised clauses over concept names `CName` and role names `Role`. -/
inductive Clause (CName Role : Type) where
  /-- `⊓ body ⊑ ⊔ head` (empty body: `⊤`, empty head: `⊥`). -/
  | gci (body head : List CName)
  /-- `a ⊑ ∃R.b`. -/
  | exRight (a : CName) (R : RoleT Role) (b : CName)
  /-- `a ⊑ ∀R.b`. -/
  | allRight (a : CName) (R : RoleT Role) (b : CName)
  /-- `R₁ ∘ … ∘ Rₙ ⊑ S`. -/
  | chain (body : List (RoleT Role)) (sup : RoleT Role)
deriving DecidableEq, Repr

abbrev Ontology (CName Role : Type) := List (Clause CName Role)

/-- An interpretation over a domain `D`. -/
structure Interp (D CName Role : Type) where
  c : CName → D → Prop
  r : Role → D → D → Prop

variable {D CName Role : Type}

/-- The relation of a role term. -/
def Interp.rt (I : Interp D CName Role) : RoleT Role → D → D → Prop
  | .pos r => I.r r
  | .inv r => fun x y => I.r r y x

@[simp] theorem Interp.rt_flip (I : Interp D CName Role) (R : RoleT Role) (x y : D) :
    I.rt R.flip x y ↔ I.rt R y x := by
  cases R <;> rfl

/-- The composition of a list of role terms (the empty list is equality). -/
def Interp.path (I : Interp D CName Role) : List (RoleT Role) → D → D → Prop
  | [] => fun x y => x = y
  | R :: Rs => fun x z => ∃ y, I.rt R x y ∧ I.path Rs y z

/-- Tarskian satisfaction of a clause. -/
def satClause (I : Interp D CName Role) : Clause CName Role → Prop
  | .gci body head => ∀ x, (∀ a ∈ body, I.c a x) → ∃ b ∈ head, I.c b x
  | .exRight a R b => ∀ x, I.c a x → ∃ y, I.rt R x y ∧ I.c b y
  | .allRight a R b => ∀ x, I.c a x → ∀ y, I.rt R x y → I.c b y
  | .chain body S => ∀ x y, I.path body x y → I.rt S x y

/-- `I` models the ontology. -/
def models (I : Interp D CName Role) (O : Ontology CName Role) : Prop :=
  ∀ cl ∈ O, satClause I cl

/-- Subsumption between concept names, over nonempty domains as
`OWL.EntailsSub`. -/
def EntailsSub (O : Ontology CName Role) (a b : CName) : Prop :=
  ∀ (D : Type) [Nonempty D] (I : Interp D CName Role),
    models I O → ∀ x, I.c a x → I.c b x

end ContextCalculus.SRI
