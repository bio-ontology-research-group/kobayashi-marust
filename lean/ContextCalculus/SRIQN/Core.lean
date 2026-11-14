import ContextCalculus.SRIQN.NormalForm
import ContextCalculus.SRIQ.ABox

/-!
# Cores and records relative to a core (stage C2, design section 2)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. The definitions are stated for a base
ontology `B` (the `SRIQ` clauses) and a list `N` of nominal names; for an
`SRIQN` ontology `O` they are used with `basePart O` and `noms O`.

A core over a finite type `K` gives each core element a type and each pair
a label. A record relative to the core is a tree node: a type and a parent,
either a tree node (`inl`, as in `SRIQ`) or a core element (`inr`, an
anchor record). A support of a record lists, besides its children, a label
to each core element (`ce`, the core entries); a core entry must not count
for any at-most clause at the core element (`Counted`).

Deviation from the note: core entries are a function `K → labels`, an
empty label meaning no entry, and empty labels are allowed. This makes the
entries distinct by construction and only enlarges the set of supports;
the soundness proof does not use nonemptiness.
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Nbr StarOK UpClosed EdgeOK cnt flipL nbrs RoleLe Closed mem_flipL)

variable {CName Role : Type}

/-- A record relative to a core over `K`. -/
abbrev RecN (CName Role K : Type) :=
  Finset CName × (Nbr CName Role ⊕ (K × Finset (RoleT Role)))

section Defs

variable [DecidableEq CName] [DecidableEq Role] (B : SRIQ.Ontology CName Role)
  (N : List CName) {K : Type} [Fintype K] (ty : K → Finset CName)

/-- An entry with label `L` and type `t` at a centre of type `u` counts for
some at-most clause there. -/
def Counted (u : Finset CName) (L : Finset (RoleT Role)) (t : Finset CName) : Prop :=
  ∃ a k R b, SRIQ.Clause.atMost a k R b ∈ B ∧ a ∈ u ∧ R ∈ L ∧ b ∈ t

/-- The parent entry of a record. -/
def parentE : (Nbr CName Role ⊕ (K × Finset (RoleT Role))) → Nbr CName Role
  | .inl e => e
  | .inr (c, L) => (L, ty c)

/-- The core entries: one entry `(ce d, ty d)` per core element with a
nonempty label. -/
noncomputable def cEntries (ce : K → Finset (RoleT Role)) : List (Nbr CName Role) :=
  ((Finset.univ.filter fun d => ce d ≠ ∅).toList).map fun d => (ce d, ty d)

/-- The record of a tree child `e` of a tree node of type `t`. -/
def childRecN (t : Finset CName) (e : Nbr CName Role) : RecN CName Role K :=
  (e.2, .inl (flipL e.1, t))

/-- The record of a tree child `e` of the core element `c`. -/
def anchorRec (c : K) (e : Nbr CName Role) : RecN CName Role K :=
  (e.2, .inr (c, flipL e.1))

/-- Core entries `ce` and children `C` support `ρ` inside `G`. -/
structure SupportsN (G : Set (RecN CName Role K)) (ρ : RecN CName Role K)
    (ce : K → Finset (RoleT Role)) (C : List (Nbr CName Role)) : Prop where
  noNom : ∀ a ∈ N, a ∉ ρ.1
  anchor : ∀ c L, ρ.2 = .inr (c, L) → ce c = ∅
  unc : ∀ d, ¬ Counted B (ty d) (flipL (ce d)) ρ.1
  star : StarOK B ρ.1 ((parentE ty ρ.2 :: cEntries ty ce) ++ C)
  kids : ∀ e ∈ C, childRecN ρ.1 e ∈ G

/-- Every record of `G` has a support inside `G`. -/
def SelfSuppN (G : Set (RecN CName Role K)) : Prop :=
  ∀ ρ ∈ G, ∃ p : (K → Finset (RoleT Role)) × List (Nbr CName Role), SupportsN B N ty G ρ p.1 p.2

/-- A record is good relative to the core types `ty`. -/
def GoodN (ρ : RecN CName Role K) : Prop :=
  ∃ G : Set (RecN CName Role K), ρ ∈ G ∧ SelfSuppN B N ty G

/-- Every nominal name lies in exactly one core type. -/
def NomOK : Prop := ∀ a ∈ N, ∃! c, a ∈ ty c

/-- The good records. -/
def goodSetN : Set (RecN CName Role K) := {ρ | GoodN B N ty ρ}

end Defs

/-- **Realisation** (design section 2.4): a core with types and symmetric
labels, every nominal name in exactly one core type, and for each core
element tree children whose anchor records are good. -/
structure RealisationN [DecidableEq CName] [DecidableEq Role] (B : SRIQ.Ontology CName Role)
    (N : List CName) (K : Type) [Fintype K] where
  ty : K → Finset CName
  lab : K → K → Finset (RoleT Role)
  symm : ∀ c d, lab d c = flipL (lab c d)
  nom : NomOK N ty
  kids : ∀ c, ∃ C : List (Nbr CName Role), StarOK B (ty c) (nbrs ty lab c ++ C) ∧
    ∀ e ∈ C, GoodN B N ty (anchorRec c e)

section Basic

variable [DecidableEq CName] [DecidableEq Role] {B : SRIQ.Ontology CName Role} {N : List CName}
  {K : Type} [Fintype K] {ty : K → Finset CName}

theorem gSN : SelfSuppN B N ty (goodSetN B N ty) := by
  rintro ρ ⟨G, hρ, hG⟩
  obtain ⟨p, hp⟩ := hG ρ hρ
  exact ⟨p, hp.noNom, hp.anchor, hp.unc, hp.star, fun e he => ⟨G, hp.kids e he, hG⟩⟩

theorem flipL_flipL (L : Finset (RoleT Role)) : flipL (flipL L) = L := by
  ext S
  rw [mem_flipL, mem_flipL, RoleT.flip_flip]

theorem flipL_empty : flipL (∅ : Finset (RoleT Role)) = ∅ := by
  simp [flipL]

theorem upClosed_flipL {L : Finset (RoleT Role)} (h : UpClosed B L) : UpClosed B (flipL L) := by
  intro R hR S hRS
  rw [mem_flipL] at hR ⊢
  exact h _ hR _ (SRIQ.roleLe_flip hRS)

theorem edgeOK_flip {t s : Finset CName} {L : Finset (RoleT Role)} (h : EdgeOK B t (L, s)) :
    EdgeOK B s (flipL L, t) := by
  intro a S c hcl
  obtain ⟨h1, h2⟩ := h a S c hcl
  refine ⟨fun hS ha => h2 (mem_flipL.1 hS) ha, fun hS ha => ?_⟩
  rw [mem_flipL, RoleT.flip_flip] at hS
  exact h1 hS ha

theorem starOK_perm' {t : Finset CName} {L L' : List (Nbr CName Role)} (hp : L.Perm L')
    (h : StarOK B t L) : StarOK B t L' := by
  have hc : ∀ R b, cnt L' R b = cnt L R b := fun R b => (hp.countP_eq _).symm
  exact ⟨h.closed, fun e he => h.edge e (hp.symm.subset he),
    fun a R b hcl ha => (hc R b).symm ▸ h.ex a R b hcl ha,
    fun a j R b hcl ha => (hc R b).symm ▸ h.atLeast a j R b hcl ha,
    fun a j R b hcl ha => (hc R b).symm ▸ h.atMost a j R b hcl ha⟩

/-- Every good record avoids the nominal names. -/
theorem good_noNom {ρ : RecN CName Role K} (h : GoodN B N ty ρ) : ∀ a ∈ N, a ∉ ρ.1 := by
  obtain ⟨G, hρ, hG⟩ := h
  obtain ⟨p, hp⟩ := hG ρ hρ
  exact hp.noNom

end Basic

/-! ## Stars with uncounted extra neighbours -/

section StarLists

variable [DecidableEq CName] [DecidableEq Role] {B : SRIQ.Ontology CName Role} {D : Type}

/-- An interpretation whose elements each have a star (a duplicate-free
list of neighbours with `StarOK`), and whose other neighbours are valid
edges that count for no at-most clause, models an ALCHIQ ontology. -/
theorem models_of_starLists' (hA : SRIQ.IsALCHIQ B) (I : Interp D CName Role)
    (typ : D → Finset CName) (htyp : ∀ a x, I.c a x ↔ a ∈ typ x)
    (lab : D → D → Finset (RoleT Role)) (hlab : ∀ R x y, R ∈ lab x y ↔ I.rt R x y)
    (E : D → List D) (hnd : ∀ x, (E x).Nodup)
    (hcomp : ∀ R x y, I.rt R x y → y ∉ E x →
      UpClosed B (lab x y) ∧ EdgeOK B (typ x) (lab x y, typ y) ∧
        ¬ Counted B (typ x) (lab x y) (typ y))
    (hstar : ∀ x, StarOK B (typ x) ((E x).map fun y => (lab x y, typ y))) : SRIQ.models I B := by
  have edge : ∀ R x y, I.rt R x y → UpClosed B (lab x y) ∧ EdgeOK B (typ x) (lab x y, typ y) := by
    intro R x y h
    by_cases hy : y ∈ E x
    · exact (hstar x).edge _ (List.mem_map_of_mem hy)
    · exact ⟨(hcomp R x y h hy).1, (hcomp R x y h hy).2.1⟩
  intro cl hcl
  rw [SRIQ.satClause_iff_satAt]
  intro x
  cases cl with
  | gci body head =>
    intro hb
    obtain ⟨b, hb', hbt⟩ := SRIQ.closed_iff.1 (hstar x).closed body head hcl
      fun a ha => (htyp a x).1 (hb a ha)
    exact ⟨b, hb', (htyp b x).2 hbt⟩
  | exRight a R b =>
    intro ha
    have h1 := (hstar x).ex a R b hcl ((htyp a x).1 ha)
    rw [SRIQ.cnt_map_star x typ lab (E x)] at h1
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
    rw [SRIQ.cnt_map_star x typ lab (E x), List.countP_eq_length_filter] at h1
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
    rw [SRIQ.cnt_map_star x typ lab (E x)] at h1
    refine le_trans (SRIQ.length_le_countP hl (fun y hy => ?_) fun y hy => ?_) h1
    · exact decide_eq_true ⟨(hlab R x y).2 (hP y hy).1, (htyp b y).1 (hP y hy).2⟩
    · by_contra hy'
      exact (hcomp R x y (hP y hy).1 hy').2.2
        ⟨a, k, R, b, hcl, (htyp a x).1 ha, (hlab R x y).2 (hP y hy).1, (htyp b y).1 (hP y hy).2⟩
  | chain body S =>
    have hlen := hA body S hcl
    match body, hlen, hcl with
    | [R], _, hcl =>
      rintro y ⟨z, hxz, rfl⟩
      exact (hlab S x z).1 ((edge R x z hxz).1 R ((hlab R x z).2 hxz) S (SRIQ.roleLe_single hcl))

end StarLists

end ContextCalculus.SRIQN
