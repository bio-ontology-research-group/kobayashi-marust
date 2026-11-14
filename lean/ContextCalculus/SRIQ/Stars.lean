import ContextCalculus.SRIQ.NormalForm
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.FinRange

/-!
# Stars: good types for ALCHIQ (stage C1, design sections 2 and 3)

`docs/V1.7.0-C1-SHIQ-DESIGN.md`. A type alone no longer decides
counting, so a node carries its whole star: its type, the label and type
of its parent, and a list of children. A record is a type with the
parent's label and type (`none` at a root). A set of records supports
itself when each record has a children list that satisfies every clause
at the centre (`StarOK`) and whose children records lie in the set.

`entailsSub_iff_star`: subsumption holds iff every good root record
that contains the left name contains the right one. From a model, the
records of its elements support themselves (`type_good`); from a good
root record, the unravelling of a self-supporting set into a tree of
paths is a model (`unravel_models`).
-/

namespace ContextCalculus.SRIQ

open ContextCalculus.SRI (RoleT Interp)

variable {CName Role : Type}

/-- Role terms over a finite set of role names are finite. -/
def roleTEquivSum : RoleT Role ≃ Role ⊕ Role where
  toFun
    | .pos r => .inl r
    | .inv r => .inr r
  invFun
    | .inl r => .pos r
    | .inr r => .inv r
  left_inv R := by cases R <;> rfl
  right_inv s := by cases s <;> rfl

instance [Fintype Role] : Fintype (RoleT Role) := Fintype.ofEquiv _ roleTEquivSum.symm

/-- A neighbour: the label from the centre to it and its type. -/
abbrev Nbr (CName Role : Type) := Finset (RoleT Role) × Finset CName

/-- A record: a type and, unless it is a root, the label to its parent and
the parent's type. -/
abbrev Rec (CName Role : Type) := Finset CName × Option (Nbr CName Role)

section Defs

variable [DecidableEq CName] [DecidableEq Role] (O : Ontology CName Role)

/-- The label is closed under super-roles. -/
def UpClosed (L : Finset (RoleT Role)) : Prop :=
  ∀ R ∈ L, ∀ S, RoleLe O R S → S ∈ L

/-- Universal restrictions hold across the edge in both directions. -/
def EdgeOK (t : Finset CName) (e : Nbr CName Role) : Prop :=
  ∀ a S c, Clause.allRight a S c ∈ O →
    (S ∈ e.1 → a ∈ t → c ∈ e.2) ∧ (S.flip ∈ e.1 → a ∈ e.2 → c ∈ t)

/-- The entries of `N` that are `R`-neighbours in `b`. -/
def cnt (N : List (Nbr CName Role)) (R : RoleT Role) (b : CName) : Nat :=
  N.countP fun e => decide (R ∈ e.1 ∧ b ∈ e.2)

/-- A centre type with its neighbours satisfies every clause at the centre. -/
structure StarOK (t : Finset CName) (N : List (Nbr CName Role)) : Prop where
  closed : Closed O t
  edge : ∀ e ∈ N, UpClosed O e.1 ∧ EdgeOK O t e
  ex : ∀ a R b, Clause.exRight a R b ∈ O → a ∈ t → 1 ≤ cnt N R b
  atLeast : ∀ a k R b, Clause.atLeast a k R b ∈ O → a ∈ t → k ≤ cnt N R b
  atMost : ∀ a k R b, Clause.atMost a k R b ∈ O → a ∈ t → cnt N R b ≤ k

/-- The reverse label. -/
def flipL (L : Finset (RoleT Role)) : Finset (RoleT Role) :=
  L.image RoleT.flip

/-- The record of a child `e` of a node of type `t`. -/
def childRec (t : Finset CName) (e : Nbr CName Role) : Rec CName Role :=
  (e.2, some (flipL e.1, t))

/-- `C` is a children list for `ρ` inside `G`. -/
def Supports (G : Set (Rec CName Role)) (ρ : Rec CName Role) (C : List (Nbr CName Role)) :
    Prop :=
  StarOK O ρ.1 (ρ.2.toList ++ C) ∧ ∀ e ∈ C, childRec ρ.1 e ∈ G

/-- Every record of `G` has a children list inside `G`. -/
def SelfSupp (G : Set (Rec CName Role)) : Prop :=
  ∀ ρ ∈ G, ∃ C, Supports O G ρ C

/-- A record is good if it lies in a self-supporting set. -/
def Good (ρ : Rec CName Role) : Prop :=
  ∃ G : Set (Rec CName Role), ρ ∈ G ∧ SelfSupp O G

end Defs

section Basic

variable [DecidableEq Role]

theorem mem_flipL {L : Finset (RoleT Role)} {S : RoleT Role} : S ∈ flipL L ↔ S.flip ∈ L := by
  simp only [flipL, Finset.mem_image]
  constructor
  · rintro ⟨R, hR, rfl⟩
    simpa using hR
  · intro h
    exact ⟨S.flip, h, RoleT.flip_flip S⟩

/-- A nodup list of `P`-elements inside `E` is at most as long as the
`P`-part of `E`. -/
theorem length_le_countP {α : Type} {l E : List α} {P : α → Bool} (hl : l.Nodup)
    (hP : ∀ y ∈ l, P y = true) (hE : l ⊆ E) : l.length ≤ E.countP P := by
  rw [List.countP_eq_length_filter]
  refine (hl.subperm fun y hy => ?_).length_le
  exact List.mem_filter.2 ⟨hE hy, hP y hy⟩

end Basic

/-! ## From a model to stars -/

section ModelToStars

-- Some lemmas carry the instances only through `typeOf` and `labelOf`.
set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable {O : Ontology CName Role} {D : Type} (I : Interp D CName Role)

/-- The type of an element. -/
noncomputable def typeOf (x : D) : Finset CName :=
  by classical exact Finset.univ.filter fun B => I.c B x

/-- The label of the pair `x, y`: the role terms from `x` to `y`. -/
noncomputable def labelOf (x y : D) : Finset (RoleT Role) :=
  by classical exact Finset.univ.filter fun S => I.rt S x y

omit [DecidableEq Role] in
theorem mem_typeOf {x : D} {b : CName} : b ∈ typeOf I x ↔ I.c b x := by
  classical
  simp [typeOf]

omit [DecidableEq CName] in
theorem mem_labelOf {x y : D} {S : RoleT Role} : S ∈ labelOf I x y ↔ I.rt S x y := by
  classical
  simp [labelOf]

theorem flipL_labelOf (x y : D) : flipL (labelOf I x y) = labelOf I y x := by
  ext S
  rw [mem_flipL, mem_labelOf, mem_labelOf, Interp.rt_flip]

/-- The record of `x` with optional parent `py`. -/
noncomputable def recAt (x : D) (py : Option D) : Rec CName Role :=
  (typeOf I x, py.map fun y => (labelOf I x y, typeOf I y))

/-- The records of a model. -/
def modelRecs : Set (Rec CName Role) :=
  {ρ | ∃ x py, ρ = recAt I x py}

variable (O) in
/-- Witnesses of the existential and at-least clauses at `x`, chosen once. -/
noncomputable def wit (x : D) : List D := by
  classical
  exact O.flatMap fun cl => match cl with
    | .exRight _ R b => if h : ∃ y, I.rt R x y ∧ I.c b y then [h.choose] else []
    | .atLeast _ k R b =>
        if h : ∃ l : List D, l.Nodup ∧ l.length = k ∧ ∀ y ∈ l, I.rt R x y ∧ I.c b y
        then h.choose else []
    | _ => []

theorem wit_ex {x : D} {a b : CName} {R : RoleT Role} (hcl : Clause.exRight a R b ∈ O)
    (h : ∃ y, I.rt R x y ∧ I.c b y) : ∃ y ∈ wit O I x, I.rt R x y ∧ I.c b y := by
  classical
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold wit
  refine List.mem_flatMap.2 ⟨_, hcl, ?_⟩
  simp only
  convert List.mem_singleton_self _
  rw [dif_pos h]

theorem wit_atLeast {x : D} {a b : CName} {k : Nat} {R : RoleT Role}
    (hcl : Clause.atLeast a k R b ∈ O)
    (h : ∃ l : List D, l.Nodup ∧ l.length = k ∧ ∀ y ∈ l, I.rt R x y ∧ I.c b y) :
    ∃ l : List D, l.Nodup ∧ l.length = k ∧ (∀ y ∈ l, I.rt R x y ∧ I.c b y) ∧
      l ⊆ wit O I x := by
  classical
  refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2, fun y hy => ?_⟩
  unfold wit
  refine List.mem_flatMap.2 ⟨_, hcl, ?_⟩
  simp only
  convert hy
  rw [dif_pos h]

/-- The children of `x` under the parent `py`: the witnesses without the
parent, without repetition. -/
noncomputable def kids (x : D) (py : Option D) : List D :=
  by classical exact (wit O I x).dedup.filter fun z => decide (py ≠ some z)

/-- All neighbour elements: the parent, then the children. -/
noncomputable def elems (x : D) (py : Option D) : List D :=
  py.toList ++ kids (O := O) I x py

theorem elems_nodup (x : D) (py : Option D) : (elems (O := O) I x py).Nodup := by
  classical
  unfold elems kids
  rw [List.nodup_append]
  refine ⟨?_, (List.nodup_dedup _).filter _, ?_⟩
  · cases py <;> simp
  · intro u hu v hv
    rw [List.mem_filter] at hv
    cases py with
    | none => simp at hu
    | some y =>
      simp only [Option.toList_some, List.mem_singleton] at hu
      subst hu
      intro he
      subst he
      simp at hv

theorem wit_subset_elems (x : D) (py : Option D) : wit O I x ⊆ elems (O := O) I x py := by
  classical
  intro z hz
  unfold elems kids
  by_cases hp : py = some z
  · subst hp
    simp
  · refine List.mem_append_right _ (List.mem_filter.2 ⟨List.mem_dedup.2 hz, ?_⟩)
    simpa using hp

/-- The entry of a neighbour element. -/
noncomputable def entry (x z : D) : Nbr CName Role := (labelOf I x z, typeOf I z)

theorem entries_eq (x : D) (py : Option D) :
    (recAt I x py).2.toList ++ (kids (O := O) I x py).map (entry I x) =
      (elems (O := O) I x py).map (entry I x) := by
  cases py <;> simp [recAt, elems, entry]

theorem cnt_elems (x : D) (py : Option D) (R : RoleT Role) (b : CName) :
    cnt ((elems (O := O) I x py).map (entry I x)) R b =
      (elems (O := O) I x py).countP (fun z => by classical exact decide (I.rt R x z ∧ I.c b z)) := by
  classical
  unfold cnt
  rw [List.countP_map]
  refine List.countP_congr fun z _ => ?_
  simp [entry, mem_labelOf, mem_typeOf]

theorem modelRecs_selfSupp (hI : models I O) : SelfSupp O (modelRecs I) := by
  classical
  rintro ρ ⟨x, py, rfl⟩
  refine ⟨(kids (O := O) I x py).map (entry I x), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [closed_iff]
    intro body head hcl hbody
    obtain ⟨b, hb, hbx⟩ := hI _ hcl x fun a ha => (mem_typeOf I).1 (hbody a ha)
    exact ⟨b, hb, (mem_typeOf I).2 hbx⟩
  · intro e he
    rw [entries_eq] at he
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 he
    refine ⟨fun R hR S hRS => ?_, fun a S c hcl => ⟨fun hS ha => ?_, fun hS ha => ?_⟩⟩
    · rw [entry, mem_labelOf] at hR ⊢
      exact roleLe_sound hI hRS x z hR
    · rw [entry, mem_labelOf] at hS
      exact (mem_typeOf I).2 (hI _ hcl x ((mem_typeOf I).1 ha) z hS)
    · rw [entry, mem_labelOf, Interp.rt_flip] at hS
      exact (mem_typeOf I).2 (hI _ hcl z ((mem_typeOf I).1 ha) x hS)
  · intro a R b hcl ha
    rw [entries_eq, cnt_elems]
    obtain ⟨y, hy, hP⟩ := wit_ex I hcl (hI _ hcl x ((mem_typeOf I).1 ha))
    exact List.countP_pos_iff.2 ⟨y, wit_subset_elems I x py hy, by simpa using hP⟩
  · intro a k R b hcl ha
    rw [entries_eq, cnt_elems]
    obtain ⟨l, hnd, hlen, hP, hsub⟩ := wit_atLeast I hcl (hI _ hcl x ((mem_typeOf I).1 ha))
    rw [← hlen]
    exact length_le_countP hnd (fun y hy => by simpa using hP y hy)
      (hsub.trans (wit_subset_elems I x py))
  · intro a k R b hcl ha
    rw [entries_eq, cnt_elems, List.countP_eq_length_filter]
    refine hI _ hcl x ((mem_typeOf I).1 ha) _ ((elems_nodup I x py).filter _) fun y hy => ?_
    simpa using (List.mem_filter.1 hy).2
  · intro e he
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 he
    refine ⟨z, some x, ?_⟩
    simp [childRec, recAt, entry, flipL_labelOf]

/-- **Model to stars.** The root record of every element of a model is good. -/
theorem type_good (hI : models I O) (x : D) : Good O (typeOf I x, none) :=
  ⟨modelRecs I, ⟨x, none, rfl⟩, modelRecs_selfSupp I hI⟩

end ModelToStars

/-! ## From stars to a model: the unravelling -/

section StarsToModel

open Classical

variable [DecidableEq CName] [DecidableEq Role]
variable {O : Ontology CName Role} {G : Set (Rec CName Role)} (hG : SelfSupp O G)
  (ρ0 : Rec CName Role)

/-- The children list chosen for each record of `G`. -/
noncomputable def ch (ρ : Rec CName Role) : List (Nbr CName Role) :=
  if h : ρ ∈ G then (hG ρ h).choose else []

theorem ch_spec {ρ : Rec CName Role} (h : ρ ∈ G) : Supports O G ρ (ch hG ρ) := by
  unfold ch
  rw [dif_pos h]
  exact (hG ρ h).choose_spec

/-- The record at a path. A path lists child indices, the last step first. -/
noncomputable def recOf : List Nat → Option (Rec CName Role)
  | [] => some ρ0
  | i :: q => (recOf q).bind fun ρ => (ch hG ρ)[i]?.map (childRec ρ.1)

theorem recOf_cons {i : Nat} {q : List Nat} {ρ' : Rec CName Role} :
    recOf hG ρ0 (i :: q) = some ρ' ↔
      ∃ ρ e, recOf hG ρ0 q = some ρ ∧ (ch hG ρ)[i]? = some e ∧ ρ' = childRec ρ.1 e := by
  simp only [recOf, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨ρ, h1, e, h2, rfl⟩
    exact ⟨ρ, e, h1, h2, rfl⟩
  · rintro ⟨ρ, e, h1, h2, rfl⟩
    exact ⟨ρ, h1, e, h2, rfl⟩

theorem recOf_mem (h0 : ρ0 ∈ G) : ∀ (p : List Nat) (ρ : Rec CName Role),
    recOf hG ρ0 p = some ρ → ρ ∈ G
  | [], ρ, h => by
    simp only [recOf, Option.some.injEq] at h
    exact h ▸ h0
  | i :: q, ρ, h => by
    obtain ⟨σ, e, h1, h2, rfl⟩ := (recOf_cons hG ρ0).1 h
    exact (ch_spec hG (recOf_mem h0 q σ h1)).2 e (List.mem_of_getElem? h2)

/-- The nodes: paths that follow the chosen children lists. -/
def Node := {p : List Nat // ∃ ρ, recOf hG ρ0 p = some ρ}

/-- `q` is an `R`-neighbour of `p` along a tree edge. -/
def Adj (R : RoleT Role) (p q : List Nat) : Prop :=
  (∃ i ρ e, q = i :: p ∧ recOf hG ρ0 p = some ρ ∧ (ch hG ρ)[i]? = some e ∧ R ∈ e.1) ∨
  (∃ i ρ e, p = i :: q ∧ recOf hG ρ0 q = some ρ ∧ (ch hG ρ)[i]? = some e ∧ R.flip ∈ e.1)

/-- The unravelling. -/
def unravel : Interp (Node hG ρ0) CName Role where
  c := fun B p => ∃ ρ, recOf hG ρ0 p.1 = some ρ ∧ B ∈ ρ.1
  r := fun r p q => Adj hG ρ0 (.pos r) p.1 q.1

theorem unravel_rt (R : RoleT Role) (p q : Node hG ρ0) :
    (unravel hG ρ0).rt R p q ↔ Adj hG ρ0 R p.1 q.1 := by
  cases R with
  | pos r => exact Iff.rfl
  | inv r =>
    show Adj hG ρ0 (.pos r) q.1 p.1 ↔ Adj hG ρ0 (.inv r) p.1 q.1
    unfold Adj
    exact Or.comm

variable {hG ρ0} in
theorem unravel_c {B : CName} {p : Node hG ρ0} {ρ : Rec CName Role}
    (hp : recOf hG ρ0 p.1 = some ρ) : (unravel hG ρ0).c B p ↔ B ∈ ρ.1 := by
  show (∃ ρ', _ ∧ _) ↔ _
  constructor
  · rintro ⟨ρ', h, hB⟩
    rw [hp, Option.some.injEq] at h
    exact h ▸ hB
  · intro h
    exact ⟨ρ, hp, h⟩

theorem ne_cons_self (i : Nat) (p : List Nat) : p ≠ i :: p := by
  intro h
  have := congrArg List.length h
  simp only [List.length_cons] at this
  omega

theorem ne_cons_cons (i j : Nat) (p : List Nat) : p ≠ i :: j :: p := by
  intro h
  have := congrArg List.length h
  simp only [List.length_cons] at this
  omega

variable {hG ρ0}

/-- The edge to the child `i`. -/
theorem adj_child {R : RoleT Role} {p : List Nat} {ρ : Rec CName Role}
    (hp : recOf hG ρ0 p = some ρ) {i : Nat} (hi : i < (ch hG ρ).length) :
    Adj hG ρ0 R p (i :: p) ↔ R ∈ ((ch hG ρ)[i]).1 := by
  constructor
  · rintro (⟨j, ρ', e, he, hρ', hj, hR⟩ | ⟨j, ρ', e, he, -, -, -⟩)
    · obtain ⟨rfl, -⟩ := List.cons.inj he
      rw [hp, Option.some.injEq] at hρ'
      subst hρ'
      rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hj
      exact hj ▸ hR
    · exact absurd he (ne_cons_cons _ _ _)
  · intro hR
    exact Or.inl ⟨i, ρ, _, rfl, hp, List.getElem?_eq_getElem hi, hR⟩

/-- The edge to the parent. -/
theorem adj_parent {R : RoleT Role} {q : List Nat} {σ : Rec CName Role}
    (hq : recOf hG ρ0 q = some σ) {i : Nat} {e : Nbr CName Role} (he : (ch hG σ)[i]? = some e) :
    Adj hG ρ0 R (i :: q) q ↔ R.flip ∈ e.1 := by
  constructor
  · rintro (⟨j, ρ', e', h', -, -, -⟩ | ⟨j, ρ', e', h', hρ', hj, hR⟩)
    · exact absurd h' (ne_cons_cons _ _ _)
    · obtain ⟨rfl, -⟩ := List.cons.inj h'
      rw [hq, Option.some.injEq] at hρ'
      subst hρ'
      rw [he, Option.some.injEq] at hj
      exact hj ▸ hR
  · intro hR
    exact Or.inr ⟨i, σ, e, rfl, hq, he, hR⟩

variable (hG ρ0)

/-- The parent path. -/
def parentL : List Nat → List (List Nat)
  | [] => []
  | _ :: q => [q]

/-- The neighbour paths of `p`: the parent, then the children. -/
noncomputable def nb (p : List Nat) (ρ : Rec CName Role) : List (List Nat) :=
  parentL p ++ (List.finRange (ch hG ρ).length).map fun i => i.val :: p

/-- The neighbour paths that are `R`-neighbours in `b`. -/
def NbP (p : List Nat) (R : RoleT Role) (b : CName) (q : List Nat) : Prop :=
  Adj hG ρ0 R p q ∧ ∃ σ, recOf hG ρ0 q = some σ ∧ b ∈ σ.1

variable {hG ρ0}

theorem nb_nodup (p : List Nat) (ρ : Rec CName Role) : (nb hG p ρ).Nodup := by
  unfold nb
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · cases p <;> simp [parentL]
  · refine (List.nodup_finRange _).map fun i j h => ?_
    exact Fin.ext (List.cons.inj h).1
  · intro u hu v hv
    cases p with
    | nil => simp [parentL] at hu
    | cons j q =>
      simp only [parentL, List.mem_singleton] at hu
      subst hu
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hv
      exact ne_cons_cons _ _ _

theorem nb_valid {p : List Nat} {ρ : Rec CName Role} (hp : recOf hG ρ0 p = some ρ)
    {q : List Nat} (hq : q ∈ nb hG p ρ) : ∃ σ, recOf hG ρ0 q = some σ := by
  unfold nb at hq
  rcases List.mem_append.1 hq with hq | hq
  · cases p with
    | nil => simp [parentL] at hq
    | cons j q' =>
      simp only [parentL, List.mem_singleton] at hq
      subst hq
      obtain ⟨σ, e, h1, -, -⟩ := (recOf_cons hG ρ0).1 hp
      exact ⟨σ, h1⟩
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hq
    exact ⟨_, (recOf_cons hG ρ0).2 ⟨ρ, _, hp, List.getElem?_eq_getElem i.2, rfl⟩⟩

theorem adj_mem_nb {p : List Nat} {ρ : Rec CName Role} (hp : recOf hG ρ0 p = some ρ)
    {R : RoleT Role} {q : List Nat} (h : Adj hG ρ0 R p q) : q ∈ nb hG p ρ := by
  unfold nb
  rcases h with ⟨i, ρ', e, rfl, hρ', hi, -⟩ | ⟨i, ρ', e, rfl, -, -, -⟩
  · rw [hp, Option.some.injEq] at hρ'
    subst hρ'
    have hlt : i < (ch hG ρ).length := (List.getElem?_eq_some_iff.1 hi).1
    exact List.mem_append_right _ (List.mem_map.2 ⟨⟨i, hlt⟩, List.mem_finRange _, rfl⟩)
  · exact List.mem_append_left _ (by simp [parentL])

/-- The neighbour paths count exactly as the star's entries. -/
theorem countP_nb (h0n : ρ0.2 = none) {p : List Nat} {ρ : Rec CName Role}
    (hp : recOf hG ρ0 p = some ρ) (R : RoleT Role) (b : CName) :
    (nb hG p ρ).countP (fun q => decide (NbP hG ρ0 p R b q)) = cnt (ρ.2.toList ++ ch hG ρ) R b := by
  unfold nb cnt
  rw [List.countP_append, List.countP_append]
  congr 1
  · cases p with
    | nil =>
      simp only [recOf, Option.some.injEq] at hp
      subst hp
      simp [parentL, h0n]
    | cons j q =>
      obtain ⟨σ, e, h1, h2, rfl⟩ := (recOf_cons hG ρ0).1 hp
      simp only [parentL, childRec, Option.toList_some, List.countP_singleton]
      congr 1
      simp only [NbP, adj_parent h1 h2, mem_flipL, h1, Option.some.injEq,
        exists_eq_left']
  · rw [List.countP_map]
    conv_rhs => rw [← List.map_get_finRange (ch hG ρ), List.countP_map]
    refine List.countP_congr fun i _ => ?_
    simp only [Function.comp_apply, decide_eq_true_eq, NbP, adj_child hp i.2,
      List.get_eq_getElem]
    have hr : recOf hG ρ0 (i.val :: p) = some (childRec ρ.1 (ch hG ρ)[i.val]) :=
      (recOf_cons hG ρ0).2 ⟨ρ, _, hp, List.getElem?_eq_getElem i.2, rfl⟩
    simp only [hr, Option.some.injEq, exists_eq_left', childRec]

variable (hG ρ0)

theorem unravel_models (h0 : ρ0 ∈ G) (h0n : ρ0.2 = none) (hA : IsALCHIQ O) :
    models (unravel hG ρ0) O := by
  -- the star of a node
  have star : ∀ (p : List Nat) (ρ : Rec CName Role), recOf hG ρ0 p = some ρ →
      StarOK O ρ.1 (ρ.2.toList ++ ch hG ρ) := fun p ρ hp =>
    (ch_spec hG (recOf_mem hG ρ0 h0 p ρ hp)).1
  have edge : ∀ (p : List Nat) (ρ : Rec CName Role), recOf hG ρ0 p = some ρ →
      ∀ i e, (ch hG ρ)[i]? = some e → UpClosed O e.1 ∧ EdgeOK O ρ.1 e := fun p ρ hp i e he =>
    (star p ρ hp).edge e (List.mem_append_right _ (List.mem_of_getElem? he))
  intro cl hcl
  cases cl with
  | gci body head =>
    rintro ⟨p, ρ, hp⟩ hbody
    obtain ⟨b, hb, hbt⟩ := closed_iff.1 (star p ρ hp).closed body head hcl
      fun a ha => (unravel_c hp).1 (hbody a ha)
    exact ⟨b, hb, (unravel_c hp).2 hbt⟩
  | exRight a R b =>
    rintro ⟨p, ρ, hp⟩ ha
    have h1 := (star p ρ hp).ex a R b hcl ((unravel_c hp).1 ha)
    rw [← countP_nb h0n hp] at h1
    obtain ⟨q, hq, hP⟩ := List.countP_pos_iff.1 h1
    obtain ⟨hadj, σ, hσ, hb⟩ := of_decide_eq_true hP
    refine ⟨⟨q, σ, hσ⟩, (unravel_rt hG ρ0 R _ _).2 hadj, (unravel_c hσ).2 hb⟩
  | allRight a S c =>
    rintro ⟨p, ρ, hp⟩ ha ⟨q, σ, hσ⟩ hpq
    rw [unravel_rt] at hpq
    rw [unravel_c hp] at ha
    rw [unravel_c hσ]
    rcases hpq with ⟨i, ρ', e, rfl, hρ', hi, hS⟩ | ⟨i, ρ', e, rfl, hρ', hi, hS⟩
    · rw [hp, Option.some.injEq] at hρ'
      subst hρ'
      obtain ⟨σ', e'', h1, h2', he⟩ := (recOf_cons hG ρ0).1 hσ
      rw [hp, Option.some.injEq] at h1
      subst h1
      rw [hi, Option.some.injEq] at h2'
      subst h2' he
      exact ((edge p ρ hp i e hi).2 a S c hcl).1 hS ha
    · rw [hσ, Option.some.injEq] at hρ'
      subst hρ'
      obtain ⟨σ', e', h1, h2, rfl⟩ := (recOf_cons hG ρ0).1 hp
      rw [hσ, Option.some.injEq] at h1
      subst h1
      rw [hi, Option.some.injEq] at h2
      subst h2
      exact ((edge q σ hσ i e hi).2 a S c hcl).2 hS ha
  | atLeast a k R b =>
    rintro ⟨p, ρ, hp⟩ ha
    have h1 := (star p ρ hp).atLeast a k R b hcl ((unravel_c hp).1 ha)
    rw [← countP_nb h0n hp, List.countP_eq_length_filter] at h1
    set l0 := ((nb hG p ρ).filter fun q => decide (NbP hG ρ0 p R b q)).take k with hl0
    have hmem : ∀ q ∈ l0, q ∈ nb hG p ρ ∧ NbP hG ρ0 p R b q := fun q hq => by
      have := List.mem_filter.1 (List.mem_of_mem_take hq)
      exact ⟨this.1, of_decide_eq_true this.2⟩
    have hval : ∀ q ∈ l0, ∃ σ, recOf hG ρ0 q = some σ := fun q hq => (hmem q hq).2.2.imp
      fun σ h => h.1
    refine ⟨l0.pmap (fun q hq => (⟨q, hq⟩ : Node hG ρ0)) hval, ?_, ?_, ?_⟩
    · refine List.Nodup.pmap (fun _ _ _ _ h => congrArg Subtype.val h) ?_
      exact List.Nodup.sublist (List.take_sublist _ _) ((nb_nodup p ρ).filter _)
    · rw [List.length_pmap, hl0, List.length_take]
      omega
    · intro y hy
      obtain ⟨q, hq, rfl⟩ := List.mem_pmap.1 hy
      obtain ⟨-, hadj, σ, hσ, hb⟩ := hmem q hq
      exact ⟨(unravel_rt hG ρ0 R _ _).2 hadj, (unravel_c hσ).2 hb⟩
  | atMost a k R b =>
    rintro ⟨p, ρ, hp⟩ ha l hnd hl
    have h1 := (star p ρ hp).atMost a k R b hcl ((unravel_c hp).1 ha)
    rw [← countP_nb h0n hp] at h1
    have key := length_le_countP (l := l.map Subtype.val) (E := nb hG p ρ)
      (P := fun q => decide (NbP hG ρ0 p R b q)) (hnd.map Subtype.val_injective) ?_ ?_
    · rw [List.length_map] at key
      exact le_trans key h1
    · intro q hq
      obtain ⟨⟨q, σ, hσ⟩, hy, rfl⟩ := List.mem_map.1 hq
      obtain ⟨hr, hc⟩ := hl _ hy
      exact decide_eq_true ⟨(unravel_rt hG ρ0 R _ _).1 hr, σ, hσ, (unravel_c hσ).1 hc⟩
    · intro q hq
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
      exact adj_mem_nb hp ((unravel_rt hG ρ0 R _ _).1 (hl y hy).1)
  | chain body S =>
    have hlen := hA body S hcl
    match body, hlen, hcl with
    | [R], _, hcl =>
      rintro x y ⟨z, hxz, rfl⟩
      have hle : RoleLe O R S := roleLe_single hcl
      rw [unravel_rt] at hxz ⊢
      rcases hxz with ⟨i, ρ, e, he, hρ, hi, hR⟩ | ⟨i, ρ, e, he, hρ, hi, hR⟩
      · exact Or.inl ⟨i, ρ, e, he, hρ, hi, (edge _ ρ hρ i e hi).1 R hR S hle⟩
      · exact Or.inr ⟨i, ρ, e, he, hρ, hi,
          (edge _ ρ hρ i e hi).1 R.flip hR S.flip (roleLe_flip hle)⟩

end StarsToModel

/-! ## The characterisation -/

section Characterisation

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]

/-- **Characterisation.** For an ALCHIQ ontology, `a ⊑ b` holds iff every
good root record that contains `a` contains `b`. -/
theorem entailsSub_iff_star (O : Ontology CName Role) (h : IsALCHIQ O) (a b : CName) :
    EntailsSub O a b ↔ ∀ t, Good O (t, none) → a ∈ t → b ∈ t := by
  constructor
  · rintro hent t ⟨G, hmem, hG⟩ hat
    haveI : Nonempty (Node hG (t, none)) := ⟨⟨[], _, rfl⟩⟩
    have := hent _ (unravel hG (t, none)) (unravel_models hG _ hmem rfl h) ⟨[], _, rfl⟩
      ((unravel_c (p := ⟨[], _, rfl⟩) rfl).2 hat)
    exact (unravel_c (p := ⟨[], _, rfl⟩) rfl).1 this
  · intro hgood D _ I hI x hax
    exact (mem_typeOf I).1 (hgood _ (type_good I hI x) ((mem_typeOf I).2 hax))

/-- A concept name is unsatisfiable iff no good root record contains it. -/
theorem unsat_iff_no_star (O : Ontology CName Role) (h : IsALCHIQ O) (a : CName) :
    (∀ (D : Type) [Nonempty D] (I : Interp D CName Role), models I O → ∀ x, ¬ I.c a x) ↔
      ∀ t, Good O (t, none) → a ∉ t := by
  constructor
  · rintro hun t ⟨G, hmem, hG⟩ hat
    haveI : Nonempty (Node hG (t, none)) := ⟨⟨[], _, rfl⟩⟩
    exact hun _ (unravel hG (t, none)) (unravel_models hG _ hmem rfl h) ⟨[], _, rfl⟩
      ((unravel_c (p := ⟨[], _, rfl⟩) rfl).2 hat)
  · intro hno D _ I hI x hax
    exact hno _ (type_good I hI x) ((mem_typeOf I).2 hax)

end Characterisation

end ContextCalculus.SRIQ

#print axioms ContextCalculus.SRIQ.type_good
#print axioms ContextCalculus.SRIQ.unravel_models
#print axioms ContextCalculus.SRIQ.entailsSub_iff_star
#print axioms ContextCalculus.SRIQ.unsat_iff_no_star
