import ContextCalculus.SRIQ.Stars
import ContextCalculus.SRIQ.Transitivity
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Basic

/-!
# SHIQ knowledge bases with an ABox (stage C1b, design sections 1 to 4)

`docs/V1.7.0-C1B-ABOX-DESIGN.md`. An ABox lists assertions about
individuals: class and role assertions, negative role assertions, and
equality and inequality of individuals. Individuals have no unique name
assumption. An interpretation of a knowledge base is an `SRI.Interp`
with a map `ind` from individuals to the domain.

* `entailsSubKB_iff` (section 2): the TBox answer does not change for a
  consistent knowledge base. A model of the knowledge base and a
  countermodel of the TBox subsumption combine into a disjoint sum.
* `consistentKB_iff_realisation` (section 3): for ALCHIQ, a knowledge
  base is consistent iff it has a realisation: blocks of individuals
  with types and labels, each block with a list of tree children whose
  records are good. A model gives a realisation by reading off the
  values of the individuals; a realisation gives a forest model whose
  trees are the unravellings of the good child records.
* `consistentKB_encTransQ` (section 4): removing transitivity keeps
  consistency when the roles of negative role assertions are simple.
-/

namespace ContextCalculus.SRIQ

open ContextCalculus.SRI (RoleT Interp)

/-! ## Section 1: assertions and knowledge bases -/

/-- An ABox assertion over individuals `Ind`. -/
inductive Assertion (CName Role Ind : Type) where
  /-- `A(a)`. -/
  | cls (a : Ind) (A : CName)
  /-- `R(a,b)`. -/
  | role (a : Ind) (R : RoleT Role) (b : Ind)
  /-- `¬R(a,b)`. -/
  | nrole (a : Ind) (R : RoleT Role) (b : Ind)
  /-- `a = b`. -/
  | same (a b : Ind)
  /-- `a ≠ b`. -/
  | diff (a b : Ind)
deriving DecidableEq, Repr

/-- An ABox: a list of assertions. -/
abbrev ABox (CName Role Ind : Type) := List (Assertion CName Role Ind)

variable {D CName Role Ind : Type}

/-- Satisfaction of an assertion by an interpretation with individuals `ind`. -/
def satAssert (I : Interp D CName Role) (ind : Ind → D) : Assertion CName Role Ind → Prop
  | .cls a X => I.c X (ind a)
  | .role a R b => I.rt R (ind a) (ind b)
  | .nrole a R b => ¬ I.rt R (ind a) (ind b)
  | .same a b => ind a = ind b
  | .diff a b => ind a ≠ ind b

/-- Every assertion holds. -/
def satABox (I : Interp D CName Role) (ind : Ind → D) (A : ABox CName Role Ind) : Prop :=
  ∀ as ∈ A, satAssert I ind as

/-- The knowledge base `(O, A)` has a model over a nonempty domain. -/
def ConsistentKB (O : Ontology CName Role) (A : ABox CName Role Ind) : Prop :=
  ∃ (D : Type) (_ : Nonempty D) (I : Interp D CName Role) (ind : Ind → D),
    models I O ∧ satABox I ind A

/-- Every model of the knowledge base has `a ⊑ b`. -/
def EntailsSubKB (O : Ontology CName Role) (A : ABox CName Role Ind) (a b : CName) : Prop :=
  ∀ (D : Type) [Nonempty D] (I : Interp D CName Role) (ind : Ind → D),
    models I O → satABox I ind A → ∀ x, I.c a x → I.c b x

/-! ## Section 2: disjoint sums -/

/-- Satisfaction of a clause at one element (for chains: on the paths
that start there). -/
def satAt (I : Interp D CName Role) (x : D) : Clause CName Role → Prop
  | .gci body head => (∀ a ∈ body, I.c a x) → ∃ b ∈ head, I.c b x
  | .exRight a R b => I.c a x → ∃ y, I.rt R x y ∧ I.c b y
  | .allRight a R b => I.c a x → ∀ y, I.rt R x y → I.c b y
  | .atLeast a n R b => I.c a x →
      ∃ l : List D, l.Nodup ∧ l.length = n ∧ ∀ y ∈ l, I.rt R x y ∧ I.c b y
  | .atMost a n R b => I.c a x →
      ∀ l : List D, l.Nodup → (∀ y ∈ l, I.rt R x y ∧ I.c b y) → l.length ≤ n
  | .chain body S => ∀ y, I.path body x y → I.rt S x y

theorem satClause_iff_satAt (I : Interp D CName Role) (cl : Clause CName Role) :
    satClause I cl ↔ ∀ x, satAt I x cl := by
  cases cl <;> exact Iff.rfl

theorem exists_eq_map {α β : Type} (f : α → β) :
    ∀ l : List β, (∀ y ∈ l, ∃ y', y = f y') → ∃ l' : List α, l = l'.map f
  | [], _ => ⟨[], rfl⟩
  | y :: l, h => by
    obtain ⟨y', rfl⟩ := h y List.mem_cons_self
    obtain ⟨l', rfl⟩ := exists_eq_map f l fun z hz => h z (List.mem_cons_of_mem _ hz)
    exact ⟨y' :: l', rfl⟩

section Embed

variable {E : Type} {K : Interp E CName Role} {I : Interp D CName Role} {f : D → E}

/-- Paths from an embedded element stay in the image. -/
theorem path_embed (hr : ∀ R x y, K.rt R (f x) y ↔ ∃ y', y = f y' ∧ I.rt R x y') :
    ∀ (body : List (RoleT Role)) (x : D) (z : E),
      K.path body (f x) z ↔ ∃ z', z = f z' ∧ I.path body x z'
  | [], x, z => by
    simp only [Interp.path]
    constructor
    · rintro rfl; exact ⟨x, rfl, rfl⟩
    · rintro ⟨z', rfl, rfl⟩; rfl
  | R :: Rs, x, z => by
    simp only [Interp.path]
    constructor
    · rintro ⟨y, hy, hp⟩
      obtain ⟨y', rfl, hy'⟩ := (hr R x y).1 hy
      obtain ⟨z', rfl, hz'⟩ := (path_embed hr Rs y' z).1 hp
      exact ⟨z', rfl, y', hy', hz'⟩
    · rintro ⟨z', rfl, y', hy', hz'⟩
      exact ⟨f y', (hr R x _).2 ⟨y', rfl, hy'⟩, (path_embed hr Rs y' _).2 ⟨z', rfl, hz'⟩⟩

/-- A clause of `I` holds in `K` at the image of an embedding whose
elements have their neighbours inside the image. -/
theorem satAt_embed (hf : Function.Injective f) (hc : ∀ a x, K.c a (f x) ↔ I.c a x)
    (hr : ∀ R x y, K.rt R (f x) y ↔ ∃ y', y = f y' ∧ I.rt R x y') {cl : Clause CName Role}
    (h : satClause I cl) (x : D) : satAt K (f x) cl := by
  rw [satClause_iff_satAt] at h
  have hx := h x
  cases cl with
  | gci body head =>
    intro hb
    obtain ⟨b, hb', hbx⟩ := hx fun a ha => (hc a x).1 (hb a ha)
    exact ⟨b, hb', (hc b x).2 hbx⟩
  | exRight a R b =>
    intro ha
    obtain ⟨y, hy, hby⟩ := hx ((hc a x).1 ha)
    exact ⟨f y, (hr R x _).2 ⟨y, rfl, hy⟩, (hc b y).2 hby⟩
  | allRight a R b =>
    intro ha y hy
    obtain ⟨y', rfl, hy'⟩ := (hr R x y).1 hy
    exact (hc b y').2 (hx ((hc a x).1 ha) y' hy')
  | atLeast a k R b =>
    intro ha
    obtain ⟨l, hnd, hlen, hl⟩ := hx ((hc a x).1 ha)
    refine ⟨l.map f, hnd.map hf, by rw [List.length_map, hlen], fun y hy => ?_⟩
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact ⟨(hr R x _).2 ⟨y', rfl, (hl y' hy').1⟩, (hc b y').2 (hl y' hy').2⟩
  | atMost a k R b =>
    intro ha l hnd hl
    obtain ⟨l', rfl⟩ := exists_eq_map f l fun y hy => ((hr R x y).1 (hl y hy).1).imp
      fun _ h => h.1
    rw [List.length_map]
    refine hx ((hc a x).1 ha) l' (List.Nodup.of_map f hnd) fun y hy => ?_
    have h1 := hl (f y) (List.mem_map_of_mem hy)
    obtain ⟨y', hy', hR⟩ := (hr R x _).1 h1.1
    obtain rfl := hf hy'
    exact ⟨hR, (hc b y).1 h1.2⟩
  | chain body S =>
    intro y hy
    obtain ⟨y', rfl, hy'⟩ := (path_embed hr body x y).1 hy
    exact (hr S x _).2 ⟨y', rfl, hx y' hy'⟩

end Embed

/-- The disjoint sum of two interpretations. -/
def sumI {D1 D2 : Type} (I : Interp D1 CName Role) (J : Interp D2 CName Role) :
    Interp (D1 ⊕ D2) CName Role where
  c a := Sum.elim (I.c a) (J.c a)
  r r x y := match x, y with
    | .inl x, .inl y => I.r r x y
    | .inr x, .inr y => J.r r x y
    | _, _ => False

section Sum

variable {D1 D2 : Type} (I : Interp D1 CName Role) (J : Interp D2 CName Role)

theorem sumI_rt_inl (R : RoleT Role) (x : D1) (y : D1 ⊕ D2) :
    (sumI I J).rt R (.inl x) y ↔ ∃ y', y = .inl y' ∧ I.rt R x y' := by
  cases y <;> cases R <;> simp [sumI, Interp.rt]

theorem sumI_rt_inr (R : RoleT Role) (x : D2) (y : D1 ⊕ D2) :
    (sumI I J).rt R (.inr x) y ↔ ∃ y', y = .inr y' ∧ J.rt R x y' := by
  cases y <;> cases R <;> simp [sumI, Interp.rt]

theorem models_sumI {O : Ontology CName Role} (hI : models I O) (hJ : models J O) :
    models (sumI I J) O := by
  intro cl hcl
  rw [satClause_iff_satAt]
  rintro (x | x)
  · exact satAt_embed Sum.inl_injective (fun _ _ => Iff.rfl) (sumI_rt_inl I J) (hI cl hcl) x
  · exact satAt_embed Sum.inr_injective (fun _ _ => Iff.rfl) (sumI_rt_inr I J) (hJ cl hcl) x

theorem satABox_sumI {A : ABox CName Role Ind} {ind : Ind → D1} (h : satABox I ind A) :
    satABox (sumI I J) (Sum.inl ∘ ind) A := by
  intro as has
  have hs := h as has
  cases as with
  | cls a X => exact hs
  | role a R b => exact (sumI_rt_inl I J R _ _).2 ⟨_, rfl, hs⟩
  | nrole a R b =>
    intro h'
    obtain ⟨y, hy, h''⟩ := (sumI_rt_inl I J R _ _).1 h'
    exact hs ((Sum.inl_injective hy) ▸ h'')
  | same a b => exact congrArg Sum.inl hs
  | diff a b => exact fun h' => hs (Sum.inl_injective h')

end Sum

/-- **The TBox answer does not change.** A subsumption follows from a
knowledge base iff the knowledge base is inconsistent or the subsumption
follows from the TBox alone. -/
theorem entailsSubKB_iff (O : Ontology CName Role) (A : ABox CName Role Ind) (a b : CName) :
    EntailsSubKB O A a b ↔ ¬ ConsistentKB O A ∨ EntailsSub O a b := by
  constructor
  · intro h
    by_cases hc : ConsistentKB O A
    · right
      obtain ⟨D1, _, I, ind, hI, hA⟩ := hc
      intro D2 _ J hJ x hx
      exact h (D1 ⊕ D2) (sumI I J) (Sum.inl ∘ ind) (models_sumI I J hI hJ)
        (satABox_sumI I J hA) (.inr x) hx
    · exact Or.inl hc
  · rintro (hn | he) D _ I ind hI hA x hx
    · exact absurd ⟨D, inferInstance, I, ind, hI, hA⟩ hn
    · exact he D I hI x hx

/-! ## Section 3: realisations -/

section RealDefs

variable [DecidableEq CName] [DecidableEq Role]

/-- The named neighbours of block `b`: one entry `(lab b c, ty c)` for each
block `c` (including `b`) with a nonempty label. -/
noncomputable def nbrs {B : Type} [Fintype B] (ty : B → Finset CName)
    (lab : B → B → Finset (RoleT Role)) (b : B) : List (Nbr CName Role) :=
  ((Finset.univ.filter fun c => lab b c ≠ ∅).toList).map fun c => (lab b c, ty c)

/-- A realisation of the knowledge base `(O, A)` over the blocks `B`. -/
structure Realisation (O : Ontology CName Role) (A : ABox CName Role Ind) (B : Type)
    [Fintype B] where
  /-- The block of each individual. -/
  blk : Ind → B
  /-- The type of each block. -/
  ty : B → Finset CName
  /-- The label between two blocks. -/
  lab : B → B → Finset (RoleT Role)
  up : ∀ b c, UpClosed O (lab b c)
  symm : ∀ b c, lab c b = flipL (lab b c)
  cls : ∀ a X, Assertion.cls a X ∈ A → X ∈ ty (blk a)
  role : ∀ a R b, Assertion.role a R b ∈ A → R ∈ lab (blk a) (blk b)
  nrole : ∀ a R b, Assertion.nrole a R b ∈ A → R ∉ lab (blk a) (blk b)
  same : ∀ a b, Assertion.same a b ∈ A → blk a = blk b
  diff : ∀ a b, Assertion.diff a b ∈ A → blk a ≠ blk b
  /-- Every block has a list of tree children with good records. -/
  kids : ∀ b, ∃ C : List (Nbr CName Role), StarOK O (ty b) (nbrs ty lab b ++ C) ∧
    ∀ e ∈ C, Good O (e.2, some (flipL e.1, ty b))

end RealDefs

/-! ### Stars of an interpretation give a model -/

section StarLists

variable [DecidableEq CName] [DecidableEq Role] {O : Ontology CName Role}

theorem cnt_map_star (x : D) (typ : D → Finset CName)
    (lab : D → D → Finset (RoleT Role)) (E : List D) (R : RoleT Role) (b : CName) :
    cnt (E.map fun y => (lab x y, typ y)) R b =
      E.countP fun y => decide (R ∈ lab x y ∧ b ∈ typ y) := by
  unfold cnt
  rw [List.countP_map]
  rfl

/-- An interpretation whose elements each have a star (a type, labels to
a duplicate-free list holding every neighbour, and `StarOK`) models an
ALCHIQ ontology. -/
theorem models_of_starLists (hA : IsALCHIQ O) (I : Interp D CName Role)
    (typ : D → Finset CName) (htyp : ∀ a x, I.c a x ↔ a ∈ typ x)
    (lab : D → D → Finset (RoleT Role)) (hlab : ∀ R x y, R ∈ lab x y ↔ I.rt R x y)
    (E : D → List D) (hnd : ∀ x, (E x).Nodup) (hcomp : ∀ R x y, I.rt R x y → y ∈ E x)
    (hstar : ∀ x, StarOK O (typ x) ((E x).map fun y => (lab x y, typ y))) : models I O := by
  have edge : ∀ R x y, I.rt R x y → UpClosed O (lab x y) ∧ EdgeOK O (typ x) (lab x y, typ y) :=
    fun R x y h => (hstar x).edge _ (List.mem_map_of_mem (hcomp R x y h))
  intro cl hcl
  rw [satClause_iff_satAt]
  intro x
  cases cl with
  | gci body head =>
    intro hb
    obtain ⟨b, hb', hbt⟩ := closed_iff.1 (hstar x).closed body head hcl
      fun a ha => (htyp a x).1 (hb a ha)
    exact ⟨b, hb', (htyp b x).2 hbt⟩
  | exRight a R b =>
    intro ha
    have h1 := (hstar x).ex a R b hcl ((htyp a x).1 ha)
    rw [cnt_map_star x typ lab (E x)] at h1
    obtain ⟨y, -, hP⟩ := List.countP_pos_iff.1 h1
    obtain ⟨h2, h3⟩ := of_decide_eq_true hP
    exact ⟨y, (hlab R x y).1 h2, (htyp b y).2 h3⟩
  | allRight a S c =>
    intro ha y hy
    have := ((edge S x y hy).2 a S c hcl).1 ((hlab S x y).2 hy) ((htyp a x).1 ha)
    exact (htyp c y).2 this
  | atLeast a k R b =>
    intro ha
    have h1 := (hstar x).atLeast a k R b hcl ((htyp a x).1 ha)
    rw [cnt_map_star x typ lab (E x), List.countP_eq_length_filter] at h1
    set l0 := ((E x).filter fun y => decide (R ∈ lab x y ∧ b ∈ typ y)).take k with hl0
    refine ⟨l0, List.Nodup.sublist (List.take_sublist _ _) ((hnd x).filter _), ?_, ?_⟩
    · rw [hl0, List.length_take]
      omega
    · intro y hy
      have := of_decide_eq_true (List.mem_filter.1 (List.mem_of_mem_take hy)).2
      exact ⟨(hlab R x y).1 this.1, (htyp b y).2 this.2⟩
  | atMost a k R b =>
    intro ha l hl hP
    have h1 := (hstar x).atMost a k R b hcl ((htyp a x).1 ha)
    rw [cnt_map_star x typ lab (E x)] at h1
    refine le_trans (length_le_countP hl (fun y hy => ?_) fun y hy => ?_) h1
    · exact decide_eq_true ⟨(hlab R x y).2 (hP y hy).1, (htyp b y).1 (hP y hy).2⟩
    · exact hcomp R x y (hP y hy).1
  | chain body S =>
    have hlen := hA body S hcl
    match body, hlen, hcl with
    | [R], _, hcl =>
      rintro y ⟨z, hxz, rfl⟩
      exact (hlab S x z).1 ((edge R x z hxz).1 R ((hlab R x z).2 hxz) S (roleLe_single hcl))

end StarLists

/-! ### From a model to a realisation -/

section FromModel

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable {O : Ontology CName Role} (I : Interp D CName Role)

/-- The star of `x` with the neighbours `E` is `StarOK` when `E` is
duplicate-free and holds every witness of `x`. -/
theorem starOK_of_model (hI : models I O) (x : D) (E : List D) (hnd : E.Nodup)
    (hw : ∀ y ∈ wit O I x, ∀ R, I.rt R x y → y ∈ E) :
    StarOK O (typeOf I x) (E.map (entry I x)) := by
  classical
  have hc : ∀ R b, cnt (E.map (entry I x)) R b =
      E.countP (fun z => decide (I.rt R x z ∧ I.c b z)) := by
    intro R b
    unfold cnt
    rw [List.countP_map]
    refine List.countP_congr fun z _ => ?_
    simp [entry, mem_labelOf, mem_typeOf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [closed_iff]
    intro body head hcl hbody
    obtain ⟨b, hb, hbx⟩ := hI _ hcl x fun a ha => (mem_typeOf I).1 (hbody a ha)
    exact ⟨b, hb, (mem_typeOf I).2 hbx⟩
  · intro e he
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 he
    refine ⟨fun R hR S hRS => ?_, fun a S c hcl => ⟨fun hS ha => ?_, fun hS ha => ?_⟩⟩
    · rw [entry, mem_labelOf] at hR ⊢
      exact roleLe_sound hI hRS x z hR
    · rw [entry, mem_labelOf] at hS
      exact (mem_typeOf I).2 (hI _ hcl x ((mem_typeOf I).1 ha) z hS)
    · rw [entry, mem_labelOf, Interp.rt_flip] at hS
      exact (mem_typeOf I).2 (hI _ hcl z ((mem_typeOf I).1 ha) x hS)
  · intro a R b hcl ha
    rw [hc]
    obtain ⟨y, hy, hP⟩ := wit_ex I hcl (hI _ hcl x ((mem_typeOf I).1 ha))
    exact List.countP_pos_iff.2 ⟨y, hw y hy R hP.1, by simpa using hP⟩
  · intro a k R b hcl ha
    rw [hc]
    obtain ⟨l, hnd', hlen, hP, hsub⟩ := wit_atLeast I hcl (hI _ hcl x ((mem_typeOf I).1 ha))
    rw [← hlen]
    exact length_le_countP hnd' (fun y hy => by simpa using hP y hy)
      fun y hy => hw y (hsub hy) R (hP y hy).1
  · intro a k R b hcl ha
    rw [hc, List.countP_eq_length_filter]
    refine hI _ hcl x ((mem_typeOf I).1 ha) _ (hnd.filter _) fun y hy => ?_
    simpa using (List.mem_filter.1 hy).2

/-- The child record of an element seen from a neighbour is good. -/
theorem good_entry (hI : models I O) (x z : D) :
    Good O ((entry I x z).2, some (flipL (entry I x z).1, typeOf I x)) := by
  refine ⟨modelRecs I, ⟨z, some x, ?_⟩, modelRecs_selfSupp I hI⟩
  simp [entry, recAt, flipL_labelOf]

variable (ind : Ind → D) (x0 : D)

/-- The blocks of a model: the values of the individuals and `x0`. -/
def blockSet : Set D := {x | x = x0 ∨ ∃ a, ind a = x}

/-- The tree children of a block: its witnesses outside the blocks. -/
noncomputable def kidsB (x : D) : List D :=
  by classical exact (wit O I x).dedup.filter fun z => decide (z ∉ blockSet ind x0)

/-- **Model to realisation.** The values of the individuals (and one more
element `x0`) form the blocks of a realisation. -/
noncomputable def realOfModel [Fintype (blockSet ind x0)] {A : ABox CName Role Ind}
    (hI : models I O) (hA : satABox I ind A) : Realisation O A (blockSet ind x0) where
  blk a := ⟨ind a, Or.inr ⟨a, rfl⟩⟩
  ty b := typeOf I b.1
  lab b c := labelOf I b.1 c.1
  up b c R hR S hRS := (mem_labelOf I).2 (roleLe_sound hI hRS _ _ ((mem_labelOf I).1 hR))
  symm b c := (flipL_labelOf I b.1 c.1).symm
  cls a X h := (mem_typeOf I).2 (hA _ h)
  role a R b h := (mem_labelOf I).2 (hA _ h)
  nrole a R b h hR := hA _ h ((mem_labelOf I).1 hR)
  same a b h := Subtype.ext (hA _ h)
  diff a b h he := hA _ h (congrArg Subtype.val he)
  kids b := by
    classical
    refine ⟨(kidsB (O := O) I ind x0 b.1).map (entry I b.1), ?_, fun e he => ?_⟩
    · set L := (Finset.univ.filter fun c : blockSet ind x0 =>
        labelOf I b.1 c.1 ≠ ∅).toList with hL
      have heq : nbrs (fun c : blockSet ind x0 => typeOf I c.1) (fun b c => labelOf I b.1 c.1) b
          ++ (kidsB (O := O) I ind x0 b.1).map (entry I b.1) =
          (L.map Subtype.val ++ kidsB (O := O) I ind x0 b.1).map (entry I b.1) := by
        simp only [nbrs, List.map_append, List.map_map, hL]
        rfl
      rw [heq]
      refine starOK_of_model I hI b.1 _ ?_ ?_
      · rw [List.nodup_append]
        refine ⟨(Finset.nodup_toList _).map Subtype.val_injective,
          ((List.nodup_dedup _).filter _), ?_⟩
        intro u hu v hv huv
        subst huv
        obtain ⟨c, -, rfl⟩ := List.mem_map.1 hu
        have := of_decide_eq_true (List.mem_filter.1 hv).2
        exact this c.2
      · intro y hy R hR
        by_cases hb : y ∈ blockSet ind x0
        · refine List.mem_append_left _ (List.mem_map.2 ⟨⟨y, hb⟩, ?_, rfl⟩)
          rw [hL, Finset.mem_toList, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun h0 => ?_⟩
          have : R ∈ labelOf I b.1 y := (mem_labelOf I).2 hR
          rw [h0] at this
          exact absurd this (Finset.notMem_empty _)
        · refine List.mem_append_right _ (List.mem_filter.2 ⟨List.mem_dedup.2 hy, ?_⟩)
          exact decide_eq_true hb
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 he
      exact good_entry I hI b.1 z

theorem blockSet_finite [Finite Ind] : (blockSet ind x0).Finite := by
  have : blockSet ind x0 = insert x0 (Set.range ind) := by
    ext x
    simp only [blockSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_range]
  rw [this]
  exact Set.Finite.insert x0 (Set.toFinite (Set.range ind))

end FromModel

end ContextCalculus.SRIQ

#print axioms ContextCalculus.SRIQ.entailsSubKB_iff
