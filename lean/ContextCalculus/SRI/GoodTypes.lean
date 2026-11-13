import ContextCalculus.SRI.NormalForm
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Relation

/-!
# Good types for ALCHI (v1.6.3 plan, section 2b, Step 1)

The SRI normal form with role chains of length one: role inclusions over
role terms with inverses. A type is a finite set of concept names. Two
types are compatible across a role term `R` when every universal
restriction along a super-role of `R` holds forward and every universal
restriction along a super-role of `R⁻` holds backward. Good types are
the members of self-realising sets; the canonical interpretation on good
types models the ontology, and the type of every element of a model is
good. This extends `CompletenessContext` (ALC) to role hierarchies and
inverses.
-/

namespace ContextCalculus.SRI

variable {CName Role : Type}

/-- The ontology has role chains of length one only (role inclusions). -/
def IsALCHI (O : Ontology CName Role) : Prop :=
  ∀ body S, Clause.chain body S ∈ O → body.length = 1

/-- One inclusion step, closed under taking inverses on both sides. -/
def RoleStep (O : Ontology CName Role) (R S : RoleT Role) : Prop :=
  Clause.chain [R] S ∈ O ∨ Clause.chain [R.flip] S.flip ∈ O

/-- `R ⊑* S`: the reflexive-transitive closure of the inclusions. -/
def RoleLe (O : Ontology CName Role) : RoleT Role → RoleT Role → Prop :=
  Relation.ReflTransGen (RoleStep O)

/-- Every gci whose body holds has a head name that holds (an empty head
is a clash, so no closed type contains its body). -/
def Closed (O : Ontology CName Role) (t : Finset CName) : Prop :=
  ∀ body head, Clause.gci body head ∈ O → (∀ a ∈ body, a ∈ t) → ∃ b ∈ head, b ∈ t

/-- Compatibility of an `R`-edge from `t` to `s`. -/
def Compat (O : Ontology CName Role) (R : RoleT Role) (t s : Finset CName) : Prop :=
  (∀ a S c, Clause.allRight a S c ∈ O → RoleLe O R S → a ∈ t → c ∈ s) ∧
  (∀ a S c, Clause.allRight a S c ∈ O → RoleLe O R.flip S → a ∈ s → c ∈ t)

/-- Every existential `t` forces has a compatible witness in `G`. -/
def RealizedIn (O : Ontology CName Role) (G : Finset (Finset CName)) (t : Finset CName) : Prop :=
  ∀ a R b, Clause.exRight a R b ∈ O → a ∈ t → ∃ s ∈ G, b ∈ s ∧ Compat O R t s

def SelfReal (O : Ontology CName Role) (G : Finset (Finset CName)) : Prop :=
  ∀ t ∈ G, Closed O t ∧ RealizedIn O G t

def Good (O : Ontology CName Role) (t : Finset CName) : Prop :=
  ∃ G : Finset (Finset CName), t ∈ G ∧ SelfReal O G

/-- The canonical interpretation on good types. -/
def canon (O : Ontology CName Role) : Interp {t : Finset CName // Good O t} CName Role where
  c := fun B x => B ∈ x.val
  r := fun r x y => Compat O (.pos r) x.val y.val

theorem roleLe_flip {O : Ontology CName Role} {R S : RoleT Role} (h : RoleLe O R S) :
    RoleLe O R.flip S.flip := by
  sorry

theorem compat_flip (O : Ontology CName Role) (R : RoleT Role) (t s : Finset CName) :
    Compat O R.flip t s ↔ Compat O R s t := by
  sorry

theorem compat_mono {O : Ontology CName Role} {R S : RoleT Role} (h : RoleLe O R S)
    {t s : Finset CName} (hc : Compat O R t s) : Compat O S t s := by
  sorry

theorem canon_rt (O : Ontology CName Role) (R : RoleT Role) (x y : {t : Finset CName // Good O t}) :
    (canon O).rt R x y ↔ Compat O R x.val y.val := by
  sorry

theorem canon_models (O : Ontology CName Role) (h : IsALCHI O) : models (canon O) O := by
  sorry

section TypeOf

variable [Fintype CName] [DecidableEq CName]

noncomputable def typeOf {D : Type} (I : Interp D CName Role) (e : D) : Finset CName :=
  by classical exact Finset.univ.filter fun B => I.c B e

theorem roleLe_sound {D : Type} {I : Interp D CName Role} {O : Ontology CName Role}
    (hI : models I O) {R S : RoleT Role} (h : RoleLe O R S) (x y : D) :
    I.rt R x y → I.rt S x y := by
  sorry

theorem type_good {D : Type} {I : Interp D CName Role} {O : Ontology CName Role}
    (hI : models I O) (e : D) : Good O (typeOf I e) := by
  sorry

/-- **Step 1.** Subsumption is decided by the good types. -/
theorem entailsSub_iff_good (O : Ontology CName Role) (h : IsALCHI O) (a b : CName) :
    EntailsSub O a b ↔ ∀ t, Good O t → a ∈ t → b ∈ t := by
  sorry

/-- A concept name is unsatisfiable iff no good type contains it. -/
theorem unsat_iff_no_good (O : Ontology CName Role) (h : IsALCHI O) (a : CName) :
    (∀ (D : Type) [Nonempty D] (I : Interp D CName Role), models I O → ∀ x, ¬ I.c a x) ↔
      ∀ t, Good O t → a ∉ t := by
  sorry

end TypeOf

end ContextCalculus.SRI
