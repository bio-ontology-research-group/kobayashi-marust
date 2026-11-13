import ContextCalculus.SRI.NormalForm
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
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
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    refine Relation.ReflTransGen.tail ih ?_
    rcases hst with h1 | h2
    · exact Or.inr (by simpa using h1)
    · exact Or.inl h2

theorem compat_flip (O : Ontology CName Role) (R : RoleT Role) (t s : Finset CName) :
    Compat O R.flip t s ↔ Compat O R s t := by
  simp only [Compat, RoleT.flip_flip]
  exact And.comm

theorem compat_mono {O : Ontology CName Role} {R S : RoleT Role} (h : RoleLe O R S)
    {t s : Finset CName} (hc : Compat O R t s) : Compat O S t s := by
  refine ⟨fun a S' c hcl hS ha => hc.1 a S' c hcl (h.trans hS) ha,
    fun a S' c hcl hS ha => hc.2 a S' c hcl ((roleLe_flip h).trans hS) ha⟩

theorem canon_rt (O : Ontology CName Role) (R : RoleT Role) (x y : {t : Finset CName // Good O t}) :
    (canon O).rt R x y ↔ Compat O R x.val y.val := by
  cases R with
  | pos r => exact Iff.rfl
  | inv r => exact (compat_flip O (.pos r) x.val y.val).symm

theorem canon_models (O : Ontology CName Role) (h : IsALCHI O) : models (canon O) O := by
  intro cl hcl
  cases cl with
  | gci body head =>
    intro x hx
    obtain ⟨G, hxG, hG⟩ := x.property
    exact (hG x.val hxG).1 body head hcl hx
  | exRight a R b =>
    intro x hx
    obtain ⟨G, hxG, hG⟩ := x.property
    obtain ⟨s, hsG, hbs, hc⟩ := (hG x.val hxG).2 a R b hcl hx
    exact ⟨⟨s, ⟨G, hsG, hG⟩⟩, (canon_rt O R _ _).2 hc, hbs⟩
  | allRight a R b =>
    intro x hx y hxy
    exact ((canon_rt O R x y).1 hxy).1 a R b hcl Relation.ReflTransGen.refl hx
  | chain body S =>
    have hlen := h body S hcl
    match body, hlen, hcl with
    | [R], _, hcl =>
      intro x y hxy
      obtain ⟨z, hxz, rfl⟩ := hxy
      have hle : RoleLe O R S := Relation.ReflTransGen.single (Or.inl hcl)
      exact (canon_rt O S x z).2 (compat_mono hle ((canon_rt O R x z).1 hxz))

section TypeOf

-- `typeOf` needs the instances; some theorems carry them only through the
-- statement, so the section-variable linter flags them.
set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName]

noncomputable def typeOf {D : Type} (I : Interp D CName Role) (e : D) : Finset CName :=
  by classical exact Finset.univ.filter fun B => I.c B e

/-- Membership in the type of an element. -/
theorem mem_typeOf {D : Type} (I : Interp D CName Role) (e : D) (b : CName) :
    b ∈ typeOf I e ↔ I.c b e := by
  classical
  simp [typeOf]

theorem roleLe_sound {D : Type} {I : Interp D CName Role} {O : Ontology CName Role}
    (hI : models I O) {R S : RoleT Role} (h : RoleLe O R S) (x y : D) :
    I.rt R x y → I.rt S x y := by
  induction h generalizing x y with
  | refl => exact id
  | tail _ hst ih =>
    intro hxy
    have hS := ih x y hxy
    rcases hst with h1 | h2
    · exact hI _ h1 x y ⟨y, hS, rfl⟩
    · have := hI _ h2 y x ⟨x, (Interp.rt_flip I _ y x).2 hS, rfl⟩
      exact (Interp.rt_flip I _ y x).1 this

theorem type_good {D : Type} {I : Interp D CName Role} {O : Ontology CName Role}
    (hI : models I O) (e : D) : Good O (typeOf I e) := by
  classical
  refine ⟨Finset.univ.filter (fun t => ∃ d : D, t = typeOf I d), ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨e, rfl⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    obtain ⟨d, rfl⟩ := ht
    refine ⟨?_, ?_⟩
    · intro body head hcl hbody
      obtain ⟨b, hbh, hb⟩ := hI _ hcl d (fun a ha => (mem_typeOf I d a).1 (hbody a ha))
      exact ⟨b, hbh, (mem_typeOf I d b).2 hb⟩
    · intro a R b hcl ha
      obtain ⟨y, hry, hby⟩ := hI _ hcl d ((mem_typeOf I d a).1 ha)
      refine ⟨typeOf I y, ?_, (mem_typeOf I y b).2 hby, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, rfl⟩
      · intro a' S c hcl' hS ha'
        exact (mem_typeOf I y c).2
          (hI _ hcl' d ((mem_typeOf I d a').1 ha') y (roleLe_sound hI hS d y hry))
      · intro a' S c hcl' hS ha'
        have hyd : I.rt R.flip y d := (Interp.rt_flip I R y d).2 hry
        exact (mem_typeOf I d c).2
          (hI _ hcl' y ((mem_typeOf I y a').1 ha') d (roleLe_sound hI hS y d hyd))

/-- **Step 1.** Subsumption is decided by the good types. -/
theorem entailsSub_iff_good (O : Ontology CName Role) (h : IsALCHI O) (a b : CName) :
    EntailsSub O a b ↔ ∀ t, Good O t → a ∈ t → b ∈ t := by
  constructor
  · intro hent t ht hat
    haveI : Nonempty {t : Finset CName // Good O t} := ⟨⟨t, ht⟩⟩
    exact hent _ (canon O) (canon_models O h) ⟨t, ht⟩ hat
  · intro hgood D _ I hI x hax
    exact (mem_typeOf I x b).1
      (hgood _ (type_good hI x) ((mem_typeOf I x a).2 hax))

/-- A concept name is unsatisfiable iff no good type contains it. -/
theorem unsat_iff_no_good (O : Ontology CName Role) (h : IsALCHI O) (a : CName) :
    (∀ (D : Type) [Nonempty D] (I : Interp D CName Role), models I O → ∀ x, ¬ I.c a x) ↔
      ∀ t, Good O t → a ∉ t := by
  constructor
  · intro hun t ht hat
    haveI : Nonempty {t : Finset CName // Good O t} := ⟨⟨t, ht⟩⟩
    exact hun _ (canon O) (canon_models O h) ⟨t, ht⟩ hat
  · intro hno D _ I hI x hax
    exact hno _ (type_good hI x) ((mem_typeOf I x a).2 hax)

end TypeOf

end ContextCalculus.SRI

#print axioms ContextCalculus.SRI.canon_models
#print axioms ContextCalculus.SRI.type_good
#print axioms ContextCalculus.SRI.entailsSub_iff_good
#print axioms ContextCalculus.SRI.unsat_iff_no_good
