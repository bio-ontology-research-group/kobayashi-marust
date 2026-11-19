import ContextCalculus.SRIQN.HintCheck
import ContextCalculus.SRIQ.FastBasic

/-!
# A hint check in time near linear in the hint and the clauses (stage H2)

`docs/V1.7.0-H1-HINTS-DESIGN.md`, requests R1, R2, R7 and the sparse cores
of `docs/V1.7.0-PLAN.md`, section 20. The decisions of `checkRedN` (stage
C3e) enumerate: `Closed` and the other bounded quantifiers over `Fin n`
resolve to instances that run over all names, the super-roles are
recomputed per label, the labels of `RawHint.toHintN` are folds over all
`lab` lines, the core conditions run over all `K × K` pairs, and the
certificate check `CertOK` decides membership in its table through an
instance that enumerates records.

This file gives the same check over a sparse hint `HintS` (an array of
types, the label lines as a list of edges, the children as a list):

* `mkSIx`: the clauses indexed once per ontology (gcis by their first body
  name, universals and counting clauses by their left name, one-step role
  inclusions by role);
* `starF`: the star condition through the index and a bit mask of the
  centre type (`starF_iff`: it is `StarOK`);
* `checkRedS`: the hint check of `checkRedN` over a sparse hint, with the
  neighbours of each core element read from its sorted edge list
  (`checkRedS_eq`: it equals `checkRedN` on the denoted hint `HintS.toN`);
* `hintPartsS`, `hintPartsNLS`: the part loops of `hintPartsN`,
  `hintPartsNL` over a sparse hint (`hintPartsS_eq`, `hintPartsNLS_eq`).

No soundness argument changes: every result is an equality with the
earlier check on the denoted hint.
-/

namespace ContextCalculus.SRIQN.HF

open ContextCalculus.SRI (RoleT)
open ContextCalculus.SRIQ (Nbr StarOK UpClosed EdgeOK cnt flipL Closed lowerL upperL mem_lowerL
  mem_upperL mem_flipL)
open ContextCalculus.SRIQ.Fast (buildIdx getL mem_buildIdx mem_buildIdx_of rc rc_lt rc_inj)
open ContextCalculus.SRIQ.Proc (QNbr)

variable {n m : Nat}

/-! ## Loops over finite sets without enumerating the type -/

/-- `p` holds at every member (a loop over the underlying list). -/
def fAll {α : Type} (s : Finset α) (p : α → Bool) : Bool :=
  Quot.liftOn s.val (fun l => l.all p) fun l l' (h : l.Perm l') => by
    apply Bool.eq_iff_iff.2
    rw [List.all_eq_true, List.all_eq_true]
    exact forall_congr' fun a => imp_congr_left h.mem_iff

theorem fAll_iff {α : Type} (s : Finset α) (p : α → Bool) :
    fAll s p = true ↔ ∀ a ∈ s, p a = true := by
  obtain ⟨⟨l⟩, hl⟩ := s
  show l.all p = true ↔ _
  rw [List.all_eq_true]
  rfl

/-- `p` holds at some member. -/
def fAny {α : Type} (s : Finset α) (p : α → Bool) : Bool :=
  Quot.liftOn s.val (fun l => l.any p) fun l l' (h : l.Perm l') => by
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true, List.any_eq_true]
    exact exists_congr fun a => and_congr_left fun _ => h.mem_iff

theorem fAny_iff {α : Type} (s : Finset α) (p : α → Bool) :
    fAny s p = true ↔ ∃ a ∈ s, p a = true := by
  obtain ⟨⟨l⟩, hl⟩ := s
  show l.any p = true ↔ _
  rw [List.any_eq_true]
  rfl

/-! ## Bit masks -/

/-- The mask of a list of names. -/
def maskL (n : Nat) (l : List (Fin n)) : Array Bool :=
  l.foldl (fun M a => M.setIfInBounds a.val true) (Array.replicate n false)

/-- Membership through a mask. -/
def memM (M : Array Bool) (a : Fin n) : Bool := M[a.val]?.getD false

theorem maskL_aux (l : List (Fin n)) : ∀ (M : Array Bool), M.size = n →
    (l.foldl (fun M a => M.setIfInBounds a.val true) M).size = n ∧
    ∀ a : Fin n, memM (l.foldl (fun M a => M.setIfInBounds a.val true) M) a =
      (memM M a || decide (a ∈ l)) := by
  induction l with
  | nil => intro M hM; simp [hM]
  | cons x l ih =>
    intro M hM
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (M.setIfInBounds x.val true) (by simp [hM])
    refine ⟨h1, fun a => ?_⟩
    rw [h2 a]
    unfold memM
    rw [Array.getElem?_setIfInBounds]
    by_cases hxa : x = a
    · subst hxa
      simp [hM]
    · have hv : x.val ≠ a.val := fun h => hxa (Fin.ext h)
      have hax : a ≠ x := fun h => hxa h.symm
      simp [hv, hax]

theorem memM_maskL (l : List (Fin n)) (a : Fin n) : memM (maskL n l) a = decide (a ∈ l) := by
  have := (maskL_aux l (Array.replicate n false) (by simp)).2 a
  unfold maskL
  rw [this]
  simp [memM]

/-- The mask of a type. -/
def mask (t : Finset (Fin n)) : Array Bool := maskL n (t.sort (· ≤ ·))

theorem memM_mask (t : Finset (Fin n)) (a : Fin n) : memM (mask t) a = decide (a ∈ t) := by
  unfold mask
  rw [memM_maskL]
  simp [Finset.mem_sort]

theorem memM_mask_iff (t : Finset (Fin n)) (a : Fin n) : memM (mask t) a = true ↔ a ∈ t := by
  rw [memM_mask, decide_eq_true_iff]

/-- A membership test, as a structure so that it is built once. -/
structure MemS (n : Nat) where
  f : Fin n → Bool

/-- Membership in a type: a scan for a small type, a hash set (built once,
linear in the type) for a large one. Stage H4: the earlier bit mask had
the size of the name table and was rebuilt at every test. -/
def memTS (t : Finset (Fin n)) : MemS n :=
  if t.card ≤ 32 then ⟨fun a => decide (a ∈ t)⟩ else
    -- a hash set of the type's list (no sort; the test does not depend on the order)
    -- (stage H5: the set is made with the capacity of the list, so it never grows)
    Quot.liftOn t.val (fun l => let H := (Std.HashSet.emptyWithCapacity l.length).insertMany l;
        (⟨fun a => H.contains a⟩ : MemS n))
      (fun l l' (h : l.Perm l') => by
        show (MemS.mk _ = MemS.mk _)
        rw [MemS.mk.injEq]
        funext a
        rw [Bool.eq_iff_iff, Std.HashSet.contains_iff_mem, Std.HashSet.contains_iff_mem,
          Std.HashSet.mem_insertMany_list, Std.HashSet.mem_insertMany_list, List.contains_iff_mem,
          List.contains_iff_mem]
        simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or]
        exact h.mem_iff)

/-- Membership in a type. -/
@[inline] def memT (t : Finset (Fin n)) : Fin n → Bool := (memTS t).f

theorem memT_iff (t : Finset (Fin n)) (a : Fin n) : memT t a = true ↔ a ∈ t := by
  unfold memT memTS
  split_ifs
  · exact decide_eq_true_iff
  · obtain ⟨⟨l⟩, hl⟩ := t
    show ((Std.HashSet.emptyWithCapacity l.length).insertMany l).contains a = true ↔
      a ∈ (⟨Quot.mk _ l, hl⟩ : Finset (Fin n))
    rw [Std.HashSet.contains_iff_mem, Std.HashSet.mem_insertMany_list, List.contains_iff_mem]
    simp only [Std.HashSet.not_mem_emptyWithCapacity, false_or]
    rfl

/-! ## The index of an ontology -/

/-- The clauses of an ontology, indexed. -/
structure SIx (n m : Nat) where
  /-- the heads of the gcis with an empty body -/
  gTop : List (List (Fin n))
  /-- first body name `↦` the gcis (body, head) -/
  gBy : Array (List (List (Fin n) × List (Fin n)))
  /-- `a ↦ (S, c)` for each `allRight a S c` -/
  allBy : Array (List (RoleT (Fin m) × Fin n))
  /-- role code `↦` one-step super-roles -/
  stepsBy : Array (List (RoleT (Fin m)))
  /-- `a ↦ (k, R, b)` for each existential (`k = 1`) and at-least clause -/
  lowBy : Array (List (Nat × RoleT (Fin m) × Fin n))
  /-- `a ↦ (k, R, b)` for each at-most clause -/
  uppBy : Array (List (Nat × RoleT (Fin m) × Fin n))

/-- A gci by its first body name. -/
def gciKey : List (Fin n) × List (Fin n) → Option (Nat × (List (Fin n) × List (Fin n)))
  | (a :: b, h) => some (a.val, (a :: b, h))
  | ([], _) => none

def allKey : SRIQ.Clause (Fin n) (Fin m) → Option (Nat × (RoleT (Fin m) × Fin n))
  | .allRight a S c => some (a.val, (S, c))
  | _ => none

def mkSIx (O : SRIQ.Ontology (Fin n) (Fin m)) : SIx n m :=
  let gl := SRI.Proc.gcis (SRIQ.sriPart O)
  { gTop := (gl.filter fun g => g.1.isEmpty).map (·.2)
    gBy := buildIdx n gciKey gl
    allBy := buildIdx n allKey O
    stepsBy := buildIdx (2 * m) (fun p => some (rc p.1, p.2)) (SRIQ.Fast.steps O)
    lowBy := buildIdx n (fun q => some (q.1.val, q.2)) (lowerL O)
    uppBy := buildIdx n (fun q => some (q.1.val, q.2)) (upperL O) }

section IxLemmas

variable {O : SRIQ.Ontology (Fin n) (Fin m)}

theorem mem_gcis' {body head : List (Fin n)} :
    (body, head) ∈ SRI.Proc.gcis (SRIQ.sriPart O) ↔ SRIQ.Clause.gci body head ∈ O := by
  rw [SRI.Proc.mem_gcis, SRIQ.mem_sriPart]
  rfl

theorem mem_gTop {h : List (Fin n)} : h ∈ (mkSIx O).gTop ↔ SRIQ.Clause.gci [] h ∈ O := by
  simp only [mkSIx, List.mem_map, List.mem_filter, List.isEmpty_iff]
  constructor
  · rintro ⟨⟨b, h'⟩, ⟨hm, hb⟩, rfl⟩
    simp only at hb
    subst hb
    exact mem_gcis'.1 hm
  · intro hh
    exact ⟨([], h), ⟨mem_gcis'.2 hh, rfl⟩, rfl⟩

theorem mem_gBy {a : Fin n} {g : List (Fin n) × List (Fin n)} :
    g ∈ getL (mkSIx O).gBy a.val ↔ (∃ r, g.1 = a :: r) ∧ SRIQ.Clause.gci g.1 g.2 ∈ O := by
  simp only [mkSIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨⟨b, h⟩, hm, he⟩
    match b, he with
    | x :: r, he =>
      simp only [gciKey, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨hx, rfl⟩ := he
      exact ⟨⟨r, by rw [Fin.ext hx]⟩, mem_gcis'.1 hm⟩
  · rintro ⟨⟨r, hr⟩, hg⟩
    obtain ⟨b, h⟩ := g
    simp only at hr hg
    subst hr
    exact ⟨(a :: r, h), mem_gcis'.2 hg, rfl⟩

theorem mem_allBy {a c : Fin n} {S : RoleT (Fin m)} :
    (S, c) ∈ getL (mkSIx O).allBy a.val ↔ SRIQ.Clause.allRight a S c ∈ O := by
  simp only [mkSIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨cl, hcl, hf⟩
    cases cl <;> simp only [allKey, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨h1, rfl, rfl⟩ := hf
    rw [Fin.ext h1] at hcl
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_stepsBy {R S : RoleT (Fin m)} :
    S ∈ getL (mkSIx O).stepsBy (rc R) ↔ SRI.RoleStep (SRIQ.sriPart O) R S := by
  simp only [mkSIx]
  rw [mem_buildIdx (rc_lt R), ← SRIQ.Fast.mem_steps]
  constructor
  · rintro ⟨⟨R', S'⟩, h, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [rc_inj h1] at h
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_lowBy {a : Fin n} {p : Nat × RoleT (Fin m) × Fin n} :
    p ∈ getL (mkSIx O).lowBy a.val ↔ (a, p) ∈ lowerL O := by
  simp only [mkSIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨q, hq, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = q.1 from (Fin.ext h1).symm]
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_uppBy {a : Fin n} {p : Nat × RoleT (Fin m) × Fin n} :
    p ∈ getL (mkSIx O).uppBy a.val ↔ (a, p) ∈ upperL O := by
  simp only [mkSIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨q, hq, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = q.1 from (Fin.ext h1).symm]
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

end IxLemmas

/-! ## The star through the index -/

/-- The label is closed under the one-step super-roles. -/
def upB (ix : SIx n m) (L : Finset (RoleT (Fin m))) : Bool :=
  fAll L fun R => (getL ix.stepsBy (rc R)).all fun S => decide (S ∈ L)

/-- The universals of the centre across an edge, with a membership test of
the neighbour's type (stage H4: an argument, so that it is built once per
edge). -/
@[noinline] def edgeAll (ix : SIx n m) (M2 : MemS n) (t : Finset (Fin n)) (e : QNbr n m) : Bool :=
  fAll t (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1 ∈ e.1) || M2.f p.2)

/-- Universals across the edge `e` from a centre of type `t` with membership test `M`. -/
@[nospecialize] def edgeB (ix : SIx n m) (M : Fin n → Bool) (t : Finset (Fin n)) (e : QNbr n m) : Bool :=
  edgeAll ix (memTS e.2) t e &&
  fAll e.2 (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1.flip ∈ e.1) || M p.2)

/-- The gcis at a type with mask `M`. -/
@[nospecialize] def closedB (ix : SIx n m) (M : Fin n → Bool) (t : Finset (Fin n)) : Bool :=
  ix.gTop.all (fun h => h.any M) &&
  fAll t (fun a => (getL ix.gBy a.val).all fun g => !(g.1.all M) || g.2.any M)

/-- `l.all M` skipping the head when it equals `a` (already known to be in `t`). -/
def bodyAll (M : Fin n → Bool) (a : Fin n) : List (Fin n) → Bool
  | [] => true
  | b :: r => (if b == a then true else M b) && r.all M

theorem bodyAll_eq {M : Fin n → Bool} {a : Fin n} (hMa : M a = true) :
    ∀ (l : List (Fin n)), bodyAll M a l = l.all M
  | [] => rfl
  | b :: r => by
    simp only [bodyAll, List.all_cons]
    by_cases h : b = a
    · subst h; simp [hMa]
    · have hb : (b == a) = false := beq_false_of_ne h
      simp [hb]

/-- `closedB` avoiding the redundant head test on `gBy[a]`. -/
@[nospecialize] def closedBF (ix : SIx n m) (M : Fin n → Bool) (t : Finset (Fin n)) : Bool :=
  ix.gTop.all (fun h => h.any M) &&
  fAll t (fun a => (getL ix.gBy a.val).all fun g => !(bodyAll M a g.1) || g.2.any M)

theorem closedBF_eq (ix : SIx n m) (t : Finset (Fin n)) :
    closedBF ix (memTS t).f t = closedB ix (memTS t).f t := by
  unfold closedBF closedB
  congr 1
  apply Bool.eq_iff_iff.2
  simp only [fAll_iff]
  refine forall₂_congr fun a ha => ?_
  have hMa : (memTS t).f a = true := (memT_iff t a).2 ha
  simp only [bodyAll_eq hMa]

/-- Active universal clauses of a type `t`. -/
def allsOf (ix : SIx n m) (t : Finset (Fin n)) : List (RoleT (Fin m) × Fin n) :=
  (SRI.Proc.toL t).flatMap fun a => getL ix.allBy a.val

theorem all_allsOf (ix : SIx n m) (t : Finset (Fin n)) (P : RoleT (Fin m) × Fin n → Bool) :
    (allsOf ix t).all P = fAll t (fun a => (getL ix.allBy a.val).all P) := by
  apply Bool.eq_iff_iff.2
  simp only [allsOf, List.all_flatMap, List.all_eq_true, SRI.Proc.mem_toL, fAll_iff]

/-- Active lower-bound clauses of a type `t`. -/
def lowsOf (ix : SIx n m) (t : Finset (Fin n)) : List (Nat × RoleT (Fin m) × Fin n) :=
  (SRI.Proc.toL t).flatMap fun a => getL ix.lowBy a.val

theorem all_lowsOf (ix : SIx n m) (t : Finset (Fin n)) (P : Nat × RoleT (Fin m) × Fin n → Bool) :
    (lowsOf ix t).all P = fAll t (fun a => (getL ix.lowBy a.val).all P) := by
  apply Bool.eq_iff_iff.2
  simp only [lowsOf, List.all_flatMap, List.all_eq_true, SRI.Proc.mem_toL, fAll_iff]

/-- Active upper-bound clauses of a type `t`. -/
def uppsOf (ix : SIx n m) (t : Finset (Fin n)) : List (Nat × RoleT (Fin m) × Fin n) :=
  (SRI.Proc.toL t).flatMap fun a => getL ix.uppBy a.val

theorem all_uppsOf (ix : SIx n m) (t : Finset (Fin n)) (P : Nat × RoleT (Fin m) × Fin n → Bool) :
    (uppsOf ix t).all P = fAll t (fun a => (getL ix.uppBy a.val).all P) := by
  apply Bool.eq_iff_iff.2
  simp only [uppsOf, List.all_flatMap, List.all_eq_true, SRI.Proc.mem_toL, fAll_iff]

/-- `decide (k ≤ l.countP p)`, using `l.any p` when `k = 1`. -/
def atLeastP {α : Type} (k : Nat) (l : List α) (p : α → Bool) : Bool :=
  if k == 1 then l.any p else decide (k ≤ l.countP p)

theorem atLeastP_eq {α : Type} (k : Nat) (l : List α) (p : α → Bool) :
    atLeastP k l p = decide (k ≤ l.countP p) := by
  unfold atLeastP
  split_ifs with hk
  · rw [beq_iff_eq] at hk
    subst hk
    apply Bool.eq_iff_iff.2
    rw [List.any_eq_true, ← List.countP_pos_iff, decide_eq_true_iff]
    omega
  · rfl

theorem cnt_map_memTS (N : List (QNbr n m)) (R : RoleT (Fin m)) (c : Fin n) :
    (N.map fun e => (e.1, memTS e.2)).countP (fun e => e.2.f c && decide (R ∈ e.1)) =
      cnt N R c := by
  unfold cnt
  rw [List.countP_map]
  refine List.countP_congr fun e _ => ?_
  simp only [Function.comp_apply, Bool.and_comm ((memTS e.2).f c), Bool.and_eq_true,
    decide_eq_true_eq]
  exact and_congr_right fun _ => memT_iff e.2 c

theorem all_comm {α β : Type} (l1 : List α) (l2 : List β) (f : α → β → Bool) :
    l1.all (fun x => l2.all fun y => f x y) = l2.all (fun y => l1.all fun x => f x y) := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true]
  exact ⟨fun h y hy x hx => h x hx y hy, fun h x hx y hy => h y hy x hx⟩

theorem if_isEmpty_all {α β γ : Type} (l1 : List α) (l2 : List β) (l3 : List γ)
    (p1 : α → Bool) (p2 : β → Bool) (p3 : γ → Bool) :
    (if l1.isEmpty && l2.isEmpty && l3.isEmpty then true
     else l1.all p1 && l2.all p2 && l3.all p3) =
    (l1.all p1 && l2.all p2 && l3.all p3) := by
  cases l1 <;> cases l2 <;> cases l3 <;> rfl

theorem all_and_combine {α : Type} (u p1 p2 : α → Bool) :
    ∀ (l : List α), (l.all (fun e => u e && p2 e) && l.all p1) = l.all (fun e => u e && (p1 e && p2 e))
  | [] => rfl
  | e :: l => by
    simp only [List.all_cons, ← all_and_combine u p1 p2 l]
    cases u e <;> cases p1 e <;> cases p2 e <;> simp

/-- **The star condition through the index.** -/
def starF (ix : SIx n m) (t : Finset (Fin n)) (N : List (QNbr n m)) : Bool :=
  -- the membership structure is bound first, so that the test is built once
  let MS := memTS t
  let M := MS.f
  closedB ix M t &&
  N.all (fun e => upB ix e.1 && edgeB ix M t e) &&
  fAll t (fun a => (getL ix.lowBy a.val).all fun q => decide (q.1 ≤ cnt N q.2.1 q.2.2)) &&
  fAll t (fun a => (getL ix.uppBy a.val).all fun q => decide (cnt N q.2.1 q.2.2 ≤ q.1))

section StarLemmas

variable {O : SRIQ.Ontology (Fin n) (Fin m)}

theorem upB_iff (L : Finset (RoleT (Fin m))) : upB (mkSIx O) L = true ↔ UpClosed O L := by
  unfold upB
  rw [fAll_iff]
  simp only [List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h R hR S hRS
    induction hRS with
    | refl => exact hR
    | tail _ hst ih => exact h _ ih _ (mem_stepsBy.2 hst)
  · intro h R hR S hS
    exact h R hR S (Relation.ReflTransGen.single (mem_stepsBy.1 hS))

theorem edgeB_iff (t : Finset (Fin n)) (e : QNbr n m) :
    edgeB (mkSIx O) (memT t) t e = true ↔ EdgeOK O t e := by
  unfold edgeB edgeAll EdgeOK
  change (fAll t (fun a => (getL (mkSIx O).allBy a.val).all fun p => !decide (p.1 ∈ e.1) ||
    memT e.2 p.2) && _) = true ↔ _
  simp only [Bool.and_eq_true, fAll_iff, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, memT_iff]
  constructor
  · rintro ⟨h1, h2⟩ a S c hcl
    refine ⟨fun hS ha => ?_, fun hS ha => ?_⟩
    · exact (h1 a ha (S, c) (mem_allBy.2 hcl)).resolve_left (not_not.2 hS)
    · exact (h2 a ha (S, c) (mem_allBy.2 hcl)).resolve_left (not_not.2 hS)
  · intro h
    refine ⟨fun a ha p hp => ?_, fun a ha p hp => ?_⟩
    · have := h a p.1 p.2 (mem_allBy.1 hp)
      by_cases hS : p.1 ∈ e.1
      · exact Or.inr (this.1 hS ha)
      · exact Or.inl hS
    · have := h a p.1 p.2 (mem_allBy.1 hp)
      by_cases hS : p.1.flip ∈ e.1
      · exact Or.inr (this.2 hS ha)
      · exact Or.inl hS

theorem closedB_iff (t : Finset (Fin n)) : closedB (mkSIx O) (memT t) t = true ↔ Closed O t := by
  unfold closedB
  rw [SRIQ.closed_iff]
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, fAll_iff, Bool.or_eq_true,
    Bool.not_eq_true', memT_iff]
  constructor
  · rintro ⟨h1, h2⟩ body head hcl hb
    cases body with
    | nil => exact h1 head (mem_gTop.2 hcl)
    | cons a r =>
      have hg : (a :: r, head) ∈ getL (mkSIx O).gBy a.val := mem_gBy.2 ⟨⟨r, rfl⟩, hcl⟩
      rcases h2 a (hb a List.mem_cons_self) _ hg with h | h
      · exfalso
        rw [List.all_eq_false] at h
        obtain ⟨x, hx, hxn⟩ := h
        simp only [memT_iff] at hxn
        exact hxn (hb x hx)
      · exact h
  · intro h
    refine ⟨fun hd hh => h [] hd (mem_gTop.1 hh) (by simp), fun a _ g hg => ?_⟩
    by_cases hb : g.1.all (memT t) = true
    · right
      rw [List.all_eq_true] at hb
      exact h g.1 g.2 (mem_gBy.1 hg).2 fun x hx => (memT_iff t x).1 (hb x hx)
    · left
      simpa using hb

/-- **The indexed star is the star.** -/
theorem starF_iff (t : Finset (Fin n)) (N : List (QNbr n m)) :
    starF (mkSIx O) t N = true ↔ StarOK O t N := by
  rw [SRIQ.Proc.starOK_iff]
  unfold starF
  change (closedB (mkSIx O) (memT t) t && N.all (fun e => upB (mkSIx O) e.1 && edgeB (mkSIx O) (memT t) t e) && _ && _) = true ↔ _
  simp only [Bool.and_eq_true, List.all_eq_true, fAll_iff, decide_eq_true_eq, closedB_iff,
    upB_iff, edgeB_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, fun q hq ht => h3 q.1 ht q.2 (mem_lowBy.2 hq),
      fun q hq ht => h4 q.1 ht q.2 (mem_uppBy.2 hq)⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, fun a ha p hp => h3 (a, p) (mem_lowBy.1 hp) ha⟩,
      fun a ha p hp => h4 (a, p) (mem_uppBy.1 hp) ha⟩

/-- `Counted` through the index. -/
def countedB (ix : SIx n m) (u : Finset (Fin n)) (L : Finset (RoleT (Fin m))) (t : Finset (Fin n)) :
    Bool :=
  fAny u fun a => (getL ix.uppBy a.val).any fun q => decide (q.2.1 ∈ L) && decide (q.2.2 ∈ t)

theorem countedB_iff (u : Finset (Fin n)) (L : Finset (RoleT (Fin m))) (t : Finset (Fin n)) :
    countedB (mkSIx O) u L t = true ↔ Counted O u L t := by
  unfold countedB Counted
  simp only [fAny_iff, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, ⟨k, R, b⟩, hp, hR, hb⟩
    exact ⟨a, k, R, b, mem_upperL.1 (mem_uppBy.1 hp), ha, hR, hb⟩
  · rintro ⟨a, k, R, b, hcl, ha, hR, hb⟩
    exact ⟨a, ha, (k, R, b), mem_uppBy.2 (mem_upperL.2 hcl), hR, hb⟩

end StarLemmas


/-! ## Edge lists merged by key -/

section Merge

variable {β : Type} [DecidableEq β]

theorem mem_foldl_union {α γ : Type} [DecidableEq γ] (p : α → Prop) [DecidablePred p]
    (f : α → Finset γ) : ∀ (l : List α) (acc : Finset γ) (x : γ),
      x ∈ l.foldl (fun acc e => if p e then acc ∪ f e else acc) acc ↔ x ∈ acc ∨ ∃ e ∈ l, p e ∧ x ∈ f e
  | [], acc, x => by simp
  | e :: l, acc, x => by
    rw [List.foldl_cons, mem_foldl_union p f l]
    by_cases he : p e
    · simp only [he, if_true, Finset.mem_union, List.mem_cons, exists_eq_or_imp, true_and]
      tauto
    · simp only [he, if_false, List.mem_cons, exists_eq_or_imp, false_and, false_or]

/-- The union of the labels with key `c`. -/
def labOf {k : Nat} (l : List (Fin k × Finset β)) (c : Fin k) : Finset β :=
  l.foldl (fun acc e => if e.1 = c then acc ∪ e.2 else acc) ∅

theorem mem_labOf {k : Nat} {l : List (Fin k × Finset β)} {c : Fin k} {x : β} :
    x ∈ labOf l c ↔ ∃ e ∈ l, e.1 = c ∧ x ∈ e.2 := by
  unfold labOf
  rw [mem_foldl_union (fun e : Fin k × Finset β => e.1 = c) (·.2)]
  simp

/-- Merge neighbouring entries with the same key. -/
def mergeRuns {k : Nat} : List (Fin k × Finset β) → List (Fin k × Finset β)
  | [] => []
  | x :: rest =>
    match mergeRuns rest with
    | y :: out => if x.1 = y.1 then (x.1, x.2 ∪ y.2) :: out else x :: y :: out
    | [] => [x]

theorem mergeRuns_mem {k : Nat} : ∀ (l : List (Fin k × Finset β)) (c : Fin k) (x : β),
    (∃ e ∈ mergeRuns l, e.1 = c ∧ x ∈ e.2) ↔ ∃ e ∈ l, e.1 = c ∧ x ∈ e.2
  | [], c, x => by simp [mergeRuns]
  | y :: rest, c, x => by
    have ih := mergeRuns_mem rest c x
    simp only [mergeRuns]
    split
    next z out hz =>
      rw [hz] at ih
      split_ifs with hyz
      · simp only [List.mem_cons, exists_eq_or_imp, Finset.mem_union] at ih ⊢
        constructor
        · rintro (⟨h1, h2 | h2⟩ | h)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr (ih.1 (Or.inl ⟨hyz ▸ h1, h2⟩))
          · exact Or.inr (ih.1 (Or.inr h))
        · rintro (⟨h1, h2⟩ | h)
          · exact Or.inl ⟨h1, Or.inl h2⟩
          · rcases ih.2 h with ⟨h1, h2⟩ | h
            · exact Or.inl ⟨hyz.trans h1, Or.inr h2⟩
            · exact Or.inr h
      · simp only [List.mem_cons, exists_eq_or_imp] at ih ⊢
        rw [ih]
    next hz =>
      rw [hz] at ih
      simp only [List.mem_cons, exists_eq_or_imp, List.not_mem_nil, false_and, exists_false,
        or_false] at ih ⊢
      rw [← ih]
      simp

theorem mergeRuns_key {k : Nat} : ∀ (l : List (Fin k × Finset β)) (e : Fin k × Finset β),
    e ∈ mergeRuns l → ∃ e' ∈ l, e'.1 = e.1
  | [], e, h => by simp [mergeRuns] at h
  | y :: rest, e, h => by
    have ih := mergeRuns_key rest
    simp only [mergeRuns] at h
    split at h
    next z out hz =>
      rw [hz] at ih
      split_ifs at h with hyz
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨y, List.mem_cons_self, rfl⟩
        · obtain ⟨e', he', hk⟩ := ih e (List.mem_cons_of_mem _ h)
          exact ⟨e', List.mem_cons_of_mem _ he', hk⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨e, List.mem_cons_self, rfl⟩
        · obtain ⟨e', he', hk⟩ := ih e h
          exact ⟨e', List.mem_cons_of_mem _ he', hk⟩
    next hz =>
      rcases List.mem_singleton.1 h with rfl
      exact ⟨e, List.mem_cons_self, rfl⟩

theorem mergeRuns_sorted {k : Nat} : ∀ (l : List (Fin k × Finset β)),
    l.Pairwise (fun x y => x.1 ≤ y.1) → (mergeRuns l).Pairwise (fun x y => x.1 < y.1)
  | [], _ => by simp [mergeRuns]
  | y :: rest, h => by
    rw [List.pairwise_cons] at h
    have ih := mergeRuns_sorted rest h.2
    have hle : ∀ e ∈ mergeRuns rest, y.1 ≤ e.1 := fun e he => by
      obtain ⟨e', he', hk⟩ := mergeRuns_key rest e he
      exact hk ▸ h.1 e' he'
    simp only [mergeRuns]
    split
    next z out hz =>
      rw [hz] at ih hle
      rw [List.pairwise_cons] at ih
      split_ifs with hyz
      · rw [List.pairwise_cons]
        exact ⟨fun e he => hyz ▸ ih.1 e he, ih.2⟩
      · have hlt : y.1 < z.1 := lt_of_le_of_ne (hle z List.mem_cons_self) hyz
        rw [List.pairwise_cons, List.pairwise_cons]
        refine ⟨fun e he => ?_, ih.1, ih.2⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact hlt
        · exact lt_trans hlt (ih.1 e he)
    next => simp

theorem eq_of_pairwise_key {k : Nat} {X : Type} : ∀ {l : List (Fin k × X)},
    l.Pairwise (fun x y => x.1 < y.1) → ∀ {e e' : Fin k × X}, e ∈ l → e' ∈ l → e.1 = e'.1 → e = e'
  | [], _, _, _, he, _, _ => by simp at he
  | x :: l, h, e, e', he, he', hk => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 he with h1 | h1 <;> rcases List.mem_cons.1 he' with h2 | h2
    · rw [h1, h2]
    · subst h1
      exact absurd (h.1 _ h2) (by rw [hk]; exact lt_irrefl _)
    · subst h2
      exact absurd (h.1 _ h1) (by rw [← hk]; exact lt_irrefl _)
    · exact eq_of_pairwise_key h.2 h1 h2 hk

/-- The entries sorted by key and merged: one entry per key. -/
def merged {k : Nat} (l : List (Fin k × Finset β)) : List (Fin k × Finset β) :=
  mergeRuns (l.mergeSort fun x y => decide (x.1 ≤ y.1))

theorem merged_sorted {k : Nat} (l : List (Fin k × Finset β)) :
    (merged l).Pairwise (fun x y => x.1 < y.1) := by
  refine mergeRuns_sorted _ ?_
  have := List.pairwise_mergeSort (le := fun x y : Fin k × Finset β => decide (x.1 ≤ y.1))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _) l
  simpa using this

theorem merged_mem {k : Nat} (l : List (Fin k × Finset β)) (c : Fin k) (x : β) :
    (∃ e ∈ merged l, e.1 = c ∧ x ∈ e.2) ↔ ∃ e ∈ l, e.1 = c ∧ x ∈ e.2 := by
  unfold merged
  rw [mergeRuns_mem]
  exact exists_congr fun e => and_congr_left fun _ => (List.mergeSort_perm _ _).mem_iff

theorem merged_lab {k : Nat} {l : List (Fin k × Finset β)} {e : Fin k × Finset β}
    (he : e ∈ merged l) : e.2 = labOf l e.1 := by
  ext x
  rw [mem_labOf, ← merged_mem]
  constructor
  · intro hx
    exact ⟨e, he, rfl, hx⟩
  · rintro ⟨e', he', hk, hx⟩
    rwa [eq_of_pairwise_key (merged_sorted l) he he' hk.symm]

/-- **One entry per key with a nonempty label.** The merged entries give
the same neighbour list as a scan over all keys, up to order. -/
theorem merged_perm {k : Nat} {X : Type} (L : Fin k → Finset β) (ty : Fin k → X)
    (l : List (Fin k × Finset β)) (hl : ∀ c, labOf l c = L c) :
    (((merged l).filter fun e => decide (e.2 ≠ ∅)).map fun e => (e.2, ty e.1)).Perm
      (((List.finRange k).filter fun c => decide (L c ≠ ∅)).map fun c => (L c, ty c)) := by
  have hmap : (((merged l).filter fun e => decide (e.2 ≠ ∅)).map fun e => (e.2, ty e.1)) =
      ((((merged l).filter fun e => decide (e.2 ≠ ∅)).map (·.1)).map fun c => (L c, ty c)) := by
    rw [List.map_map]
    refine List.map_congr_left fun e he => ?_
    have := merged_lab (List.mem_filter.1 he).1
    simp only [Function.comp_apply]
    rw [this, hl]
  rw [hmap]
  refine List.Perm.map _ (SRIQ.Proc.perm_of_nodup_mem ?_ ((List.nodup_finRange _).filter _) ?_)
  · have hp := (merged_sorted l).sublist (List.filter_sublist (p := fun e => decide (e.2 ≠ ∅)))
    have := hp.map (·.1) (R := fun x y : Fin k × Finset β => x.1 < y.1) (S := fun a b : Fin k => a < b)
      (fun _ _ h => h)
    exact this.imp ne_of_lt
  · intro c
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange, true_and]
    constructor
    · rintro ⟨e, ⟨he, hne⟩, rfl⟩
      rwa [← hl, ← merged_lab he]
    · intro hne
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hne
      rw [← hl, mem_labOf, ← merged_mem] at hx
      obtain ⟨e, he, hk, hx⟩ := hx
      exact ⟨e, ⟨he, Finset.ne_empty_of_mem hx⟩, hk⟩

end Merge

/-! ## Sparse hints -/

/-- A certificate row with its core entries as a list. -/
structure RecS (n m k : Nat) where
  ty : Finset (Fin n)
  par : Nbr (Fin n) (Fin m) ⊕ (Fin k × Finset (RoleT (Fin m)))
  ce : List (Fin k × Finset (RoleT (Fin m)))
  kids : List (QNbr n m)

/-- The row of `Proc.HintN`. -/
def RecS.toN {k : Nat} (r : RecS n m k) :
    Proc.NRec n m k × (Fin k → Finset (RoleT (Fin m))) × List (QNbr n m) :=
  ((r.ty, r.par), labOf r.ce, r.kids)

/-- **A sparse hint**: the core types as an array, the labels as a list of
edges (an absent pair has the empty label; the label back is completed
with the inverses), the children of core elements as a list. -/
structure HintS (n m : Nat) where
  k : Nat
  ty : Array (Finset (Fin n))
  lab : List (Fin k × Fin k × Finset (RoleT (Fin m)))
  kids : List (Fin k × QNbr n m)
  recs : List (RecS n m k)
  /-- The data part the hint names (`(cell, group, count)` lines), when
  `partNamed`; the denoted hint does not depend on it. -/
  part : List (Nat × Nat × Nat) := []
  partNamed : Bool := false
  /-- Data stars given per core element: `(element, data properties, data
  atoms)` entries; `dgiven` the elements whose star is given. -/
  dstar : List (Nat × List Nat × List Nat) := []
  dgiven : List Nat := []

namespace HintS

variable (h : HintS n m)

def tyF (b : Fin h.k) : Finset (Fin n) := h.ty[b.val]?.getD ∅

/-- The label lines from `b` to `c`. -/
def half (b c : Fin h.k) : Finset (RoleT (Fin m)) :=
  h.lab.foldl (fun acc e => if e.1 = b ∧ e.2.1 = c then acc ∪ e.2.2 else acc) ∅

/-- **The denoted hint.** -/
def toN : Proc.HintN n m where
  k := h.k
  ty := h.tyF
  lab := fun b c => h.half b c ∪ flipL (h.half c b)
  kids := fun b => (h.kids.filter fun e => e.1 = b).map (·.2)
  recs := h.recs.map RecS.toN

/-- The edges by core element, in both directions. -/
def adj : Array (List (Fin h.k × Finset (RoleT (Fin m)))) :=
  buildIdx h.k some (h.lab.flatMap fun e => [(e.1.val, (e.2.1, e.2.2)), (e.2.1.val, (e.1, flipL e.2.2))])

/-- The children by core element. -/
def kidIdx : Array (List (QNbr n m)) := buildIdx h.k (fun e => some (e.1.val, e.2)) h.kids

/-- The neighbours of a core element. -/
def starL (A : Array (List (Fin h.k × Finset (RoleT (Fin m))))) (b : Fin h.k) : List (QNbr n m) :=
  ((merged (getL A b.val)).filter fun e => decide (e.2 ≠ ∅)).map fun e => (e.2, h.tyF e.1)

/-- The core entries of a row. -/
def ceL (r : RecS n m h.k) : List (QNbr n m) :=
  ((merged r.ce).filter fun e => decide (e.2 ≠ ∅)).map fun e => (e.2, h.tyF e.1)

end HintS

section HintSLemmas

variable (h : HintS n m)

theorem mem_half {b c : Fin h.k} {x : RoleT (Fin m)} :
    x ∈ h.half b c ↔ ∃ e ∈ h.lab, e.1 = b ∧ e.2.1 = c ∧ x ∈ e.2.2 := by
  unfold HintS.half
  rw [mem_foldl_union (fun e : Fin h.k × Fin h.k × Finset (RoleT (Fin m)) => e.1 = b ∧ e.2.1 = c)
    (·.2.2)]
  simp [and_assoc]

theorem toN_symm (b c : Fin h.k) : h.toN.lab c b = flipL (h.toN.lab b c) := by
  simp only [HintS.toN, flipL, Finset.image_union]
  rw [show (Finset.image RoleT.flip (Finset.image RoleT.flip (h.half c b))) = h.half c b from
    SRIQN.flipL_flipL _, Finset.union_comm]

theorem mem_adj {b c : Fin h.k} {L : Finset (RoleT (Fin m))} :
    (c, L) ∈ getL h.adj b.val ↔ ∃ e ∈ h.lab,
      (e.1 = b ∧ e.2.1 = c ∧ e.2.2 = L) ∨ (e.2.1 = b ∧ e.1 = c ∧ flipL e.2.2 = L) := by
  unfold HintS.adj
  rw [mem_buildIdx b.isLt]
  simp only [List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false, Option.some.injEq]
  constructor
  · rintro ⟨y, ⟨e, he, hy⟩, hye⟩
    refine ⟨e, he, ?_⟩
    rcases hy with rfl | rfl
    · simp only [Prod.mk.injEq] at hye
      obtain ⟨h1, h2, h3⟩ := hye
      exact Or.inl ⟨Fin.ext h1, h2, h3⟩
    · simp only [Prod.mk.injEq] at hye
      obtain ⟨h1, h2, h3⟩ := hye
      exact Or.inr ⟨Fin.ext h1, h2, h3⟩
  · rintro ⟨e, he, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨_, ⟨e, he, Or.inl rfl⟩, rfl⟩
    · exact ⟨_, ⟨e, he, Or.inr rfl⟩, rfl⟩

theorem labOf_adj (b c : Fin h.k) : labOf (getL h.adj b.val) c = h.toN.lab b c := by
  ext x
  rw [mem_labOf]
  simp only [HintS.toN, Finset.mem_union, mem_flipL, mem_half]
  constructor
  · rintro ⟨⟨c', L⟩, he, rfl, hx⟩
    obtain ⟨e, he', ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩⟩ := (mem_adj h).1 he
    · exact Or.inl ⟨e, he', h1, h2, hx⟩
    · exact Or.inr ⟨e, he', h2, h1, mem_flipL.1 hx⟩
  · rintro (⟨e, he, h1, h2, hx⟩ | ⟨e, he, h1, h2, hx⟩)
    · exact ⟨(c, e.2.2), (mem_adj h).2 ⟨e, he, Or.inl ⟨h1, h2, rfl⟩⟩, rfl, hx⟩
    · exact ⟨(c, flipL e.2.2), (mem_adj h).2 ⟨e, he, Or.inr ⟨h2, h1, rfl⟩⟩, rfl, mem_flipL.2 hx⟩

theorem starL_perm (b : Fin h.k) :
    (h.starL h.adj b).Perm (SRIQ.Proc.nbrsL h.toN.ty h.toN.lab b) :=
  merged_perm _ _ _ (labOf_adj h b)

theorem getL_foldl_kids (b : Fin h.k) : ∀ (l : List (Fin h.k × QNbr n m)) (acc : Array (List (QNbr n m))),
    acc.size = h.k →
    getL (l.foldl (fun acc x => match (fun e : Fin h.k × QNbr n m => some (e.1.val, e.2)) x with
        | some (i, c) => acc.modify i (c :: ·)
        | none => acc) acc) b.val =
      ((l.filter fun e => e.1 = b).map (·.2)).reverse ++ getL acc b.val
  | [], acc, _ => by simp
  | x :: l, acc, hs => by
    rw [List.foldl_cons, getL_foldl_kids b l _ (by simpa using hs)]
    simp only [SRIQ.Fast.getL_modify, hs, b.isLt, and_true]
    by_cases hx : x.1 = b
    · have hv : x.1.val = b.val := by rw [hx]
      simp [hx]
    · have hv : ¬ x.1.val = b.val := fun hv => hx (Fin.ext hv)
      simp [hx, hv]

theorem kidIdx_perm (b : Fin h.k) : (getL h.kidIdx b.val).Perm (h.toN.kids b) := by
  unfold HintS.kidIdx buildIdx
  rw [getL_foldl_kids h b h.kids _ (by simp)]
  simp only [SRIQ.Fast.getL, Array.getElem?_replicate, b.isLt, if_true, Option.getD_some,
    List.append_nil]
  exact List.reverse_perm _

end HintSLemmas

/-- Adjacency list lookup from a precomputed array. -/
def adjFrom {k m : Nat} (A : Array (List (Fin k × Finset (RoleT (Fin m))))) (b : Fin k) :
    List (Fin k × Finset (RoleT (Fin m))) :=
  getL A b.val

/-- Edge label lookup from a precomputed adjacency array. -/
def labFrom {k m : Nat} (A : Array (List (Fin k × Finset (RoleT (Fin m))))) (b c : Fin k) :
    Finset (RoleT (Fin m)) :=
  labOf (getL A b.val) c

/-- `HintS.toN` with `lab` backed by the precomputed adjacency array `h.adj`. -/
def HintS.toNF (h : HintS n m) : Proc.HintN n m where
  k := h.k
  ty := h.tyF
  lab := labFrom h.adj
  kids := fun b => (h.kids.filter fun e => e.1 = b).map (·.2)
  recs := h.recs.map RecS.toN

@[csimp] theorem toN_eq_F : @HintS.toN = @HintS.toNF := by
  funext n m h
  unfold HintS.toN HintS.toNF
  congr 1
  funext b c
  exact (labOf_adj h b c).symm


/-! ## The data-star test over the data clauses only -/

/-- A data clause (not an object clause). -/
def isDataC {n m p q : Nat} : SRIQD.Clause (Fin n) (Fin m) (Fin p) (Fin q) → Bool
  | .obj _ => false
  | _ => true

/-- The data clauses of an ontology: the data-star test reads nothing else. -/
def dataOnly {n m p q : Nat} (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) :
    SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q) :=
  O.filter isDataC

theorem filterMap_filter_of {α β : Type} (f : α → Option β) (pr : α → Bool)
    (h : ∀ x, pr x = false → f x = none) : ∀ l : List α, (l.filter pr).filterMap f = l.filterMap f
  | [] => rfl
  | x :: l => by
    by_cases hx : pr x = true
    · simp [List.filter_cons, hx, List.filterMap_cons, filterMap_filter_of f pr h l]
    · have hn := h x (by simpa using hx)
      simp [List.filter_cons, hx, List.filterMap_cons, hn, filterMap_filter_of f pr h l]

theorem dataSatB_dataOnly {n m p q : Nat} (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) :
    SRIQD.Proc.dataSatB (dataOnly O) card = SRIQD.Proc.dataSatB O card := by
  have hL : SRIQD.dLowerL (dataOnly O) = SRIQD.dLowerL O :=
    filterMap_filter_of _ _ (fun x hx => by cases x <;> simp_all [isDataC]) O
  have hU : SRIQD.dUpperL (dataOnly O) = SRIQD.dUpperL O :=
    filterMap_filter_of _ _ (fun x hx => by cases x <;> simp_all [isDataC]) O
  have hA : SRIQD.dAllL (dataOnly O) = SRIQD.dAllL O :=
    filterMap_filter_of _ _ (fun x hx => by cases x <;> simp_all [isDataC]) O
  have hS : SRIQD.dSubL (dataOnly O) = SRIQD.dSubL O :=
    filterMap_filter_of _ _ (fun x hx => by cases x <;> simp_all [isDataC]) O
  have hc : ∀ t, SRIQD.Proc.dcands (dataOnly O) card t = SRIQD.Proc.dcands O card t := by
    intro t
    ext e
    simp only [SRIQD.Proc.dcands, Finset.mem_filter, Finset.mem_univ, true_and,
      SRIQD.Proc.dcandOK, SRIQD.DDown, SRIQD.dcontrib, hL, hU, hA, hS]
  funext t
  apply Bool.eq_iff_iff.2
  simp only [SRIQD.Proc.dataSatB, decide_eq_true_eq, SRIQD.Proc.DataSatS, SRIQD.dok_iff, hc,
    SRIQD.dbnd, SRIQD.DDown, SRIQD.DLower, hL, hU, hA, hS]

/-! ## The checks over a sparse hint -/

/-- Membership in a list through `DecidableEq`, as a loop. -/
def memB {α : Type} [DecidableEq α] (G : List α) (x : α) : Bool := G.any fun y => decide (y = x)

theorem memB_iff {α : Type} [DecidableEq α] (G : List α) (x : α) : memB G x = true ↔ x ∈ G := by
  unfold memB
  rw [List.any_eq_true]
  simp

section Checks

open ContextCalculus.SRIQN.Proc (NRec coreOKN CertOK recOK ceOK MemL memL_iff cEntriesL)

variable (h : HintS n m)

/-- Each nominal name of `N` at exactly one core element: the owners of
each name, from one pass over the core types. -/
def nomOKS0 (N : List (Fin n)) : Bool :=
  let nm := maskL n N
  let own := buildIdx n some ((List.finRange h.k).flatMap fun b =>
    (SRI.Proc.toL (h.tyF b)).filterMap fun a => if memM nm a then some (a.val, b) else none)
  N.all fun a => match getL own a.val with
    | [] => false
    | b :: rest => rest.all (· = b)

theorem nomOKS0_iff (N : List (Fin n)) : nomOKS0 h N = true ↔ NomOK N h.toN.ty := by
  unfold nomOKS0 NomOK
  simp only [List.all_eq_true]
  have hown : ∀ a ∈ N, ∀ b, b ∈ getL (buildIdx n some ((List.finRange h.k).flatMap fun b =>
      (SRI.Proc.toL (h.tyF b)).filterMap fun a =>
        if memM (maskL n N) a then some (a.val, b) else none)) a.val ↔ a ∈ h.toN.ty b := by
    intro a ha b
    rw [mem_buildIdx a.isLt]
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
      Option.some.injEq, SRI.Proc.mem_toL, memM_maskL]
    constructor
    · rintro ⟨_, ⟨b', a', ha', hif⟩, rfl⟩
      by_cases hm : a' ∈ N
      · simp only [hm, decide_true, if_true, Option.some.injEq, Prod.mk.injEq] at hif
        obtain ⟨h1, rfl⟩ := hif
        rw [show a = a' from (Fin.ext h1).symm]
        exact ha'
      · simp [hm] at hif
    · intro hb
      exact ⟨_, ⟨b, a, hb, by simp [ha]⟩, rfl⟩
  refine forall_congr' fun a => forall_congr' fun ha => ?_
  have hm := hown a ha
  generalize getL _ a.val = l at hm
  cases l with
  | nil =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨c, hc, -⟩
    exact absurd ((hm c).2 hc) (List.not_mem_nil)
  | cons b rest =>
    simp only [List.all_eq_true, decide_eq_true_eq]
    constructor
    · intro hr
      refine ⟨b, (hm b).1 List.mem_cons_self, fun c hc => ?_⟩
      rcases List.mem_cons.1 ((hm c).2 hc) with rfl | hc'
      · rfl
      · exact hr c hc'
    · rintro ⟨c, hc, hu⟩ x hx
      rw [hu x ((hm x).1 (List.mem_cons_of_mem _ hx)), hu b ((hm b).1 List.mem_cons_self)]


/-- Each nominal name at exactly one core element (no pass over the types
when there are no nominals; stage H4). -/
def nomOKS (N : List (Fin n)) : Bool := N.isEmpty || nomOKS0 h N

theorem nomOKS_iff (N : List (Fin n)) : nomOKS h N = true ↔ NomOK N h.toN.ty := by
  unfold nomOKS
  rw [Bool.or_eq_true, nomOKS0_iff]
  constructor
  · rintro (hN | hN)
    · rw [List.isEmpty_iff.1 hN]; intro a ha; cases ha
    · exact hN
  · exact Or.inr
/-- The core conditions and the stars of the core elements. -/
def coreB (ix : SIx n m) (N : List (Fin n)) : Bool :=
  let A := h.adj
  let kb := h.kidIdx
  decide (0 < h.k) && nomOKS h N &&
    (List.finRange h.k).all fun b => starF ix (h.tyF b) (h.starL A b ++ getL kb b.val)

structure MemBox (n : Nat) where
  f : Fin n → Bool
  empty : Bool

@[noinline] def mkMemBox (t : Finset (Fin n)) : MemBox n :=
  ⟨(memTS t).f, false⟩

def getMem (memA : Array (MemBox n)) (c : Fin h.k) : MemS n :=
  ⟨(memA[c.val]?.getD (mkMemBox (h.tyF c))).f⟩

theorem getMem_eq (c : Fin h.k) :
    getMem h (Array.ofFn fun b : Fin h.k => mkMemBox (h.tyF b)) c = memTS (h.tyF c) := by
  unfold getMem mkMemBox
  rw [Array.getElem?_ofFn]
  simp [c.isLt]

instance instHashableRoleTF {m : Nat} : Hashable (RoleT (Fin m)) where
  hash
    | .pos r => mixHash 1 (hash r.val)
    | .inv r => mixHash 2 (hash r.val)

def addAllP {n m : Nat} (p : RoleT (Fin m) × Fin n)
    (mp : Std.HashMap (RoleT (Fin m)) (List (Fin n))) :
    Std.HashMap (RoleT (Fin m)) (List (Fin n)) :=
  mp.insert p.1 (p.2 :: (mp[p.1]?).getD [])

def allsMapOf {n m : Nat} (ps : List (RoleT (Fin m) × Fin n)) :
    Std.HashMap (RoleT (Fin m)) (List (Fin n)) :=
  ps.reverse.foldl (fun mp p => addAllP p mp) ∅

theorem foldr_addAllP {n m : Nat} (R : RoleT (Fin m)) (c : Fin n) :
    ∀ (ps : List (RoleT (Fin m) × Fin n)),
      c ∈ ((ps.foldr addAllP ∅)[R]?).getD [] ↔ (R, c) ∈ ps
  | [] => by simp
  | (S, d) :: ps => by
    simp only [List.foldr_cons, addAllP, Std.HashMap.getElem?_insert, List.mem_cons, Prod.mk.injEq]
    by_cases h : S = R
    · subst h
      simp [foldr_addAllP S c ps]
    · have hRS : R ≠ S := Ne.symm h
      simp [h, hRS, foldr_addAllP R c ps]

theorem mem_allsMapOf {n m : Nat} (ps : List (RoleT (Fin m) × Fin n))
    (R : RoleT (Fin m)) (c : Fin n) :
    c ∈ ((allsMapOf ps)[R]?).getD [] ↔ (R, c) ∈ ps := by
  unfold allsMapOf
  rw [← List.foldr_eq_foldl_reverse]
  exact foldr_addAllP R c ps

def checkAllsFwd {n m : Nat} (mp : Std.HashMap (RoleT (Fin m)) (List (Fin n)))
    (L : Finset (RoleT (Fin m))) (M : Fin n → Bool) : Bool :=
  fAll L fun R => ((mp[R]?).getD []).all M

theorem checkAllsFwd_eq {n m : Nat} (ps : List (RoleT (Fin m) × Fin n))
    (L : Finset (RoleT (Fin m))) (M : Fin n → Bool) :
    checkAllsFwd (allsMapOf ps) L M = ps.all (fun p => !decide (p.1 ∈ L) || M p.2) := by
  apply Bool.eq_iff_iff.2
  unfold checkAllsFwd
  simp only [fAll_iff, List.all_eq_true, mem_allsMapOf, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h ⟨R, c⟩ hp
    by_cases hR : R ∈ L
    · exact Or.inr (h R hR c hp)
    · exact Or.inl hR
  · intro h R hR c hp
    exact (h (R, c) hp).resolve_left (not_not.2 hR)

def checkAllsBwd {n m : Nat} (mp : Std.HashMap (RoleT (Fin m)) (List (Fin n)))
    (L : Finset (RoleT (Fin m))) (M : Fin n → Bool) : Bool :=
  fAll L fun R => ((mp[R.flip]?).getD []).all M

theorem checkAllsBwd_eq {n m : Nat} (ps : List (RoleT (Fin m) × Fin n))
    (L : Finset (RoleT (Fin m))) (M : Fin n → Bool) :
    checkAllsBwd (allsMapOf ps) L M = ps.all (fun p => !decide (p.1.flip ∈ L) || M p.2) := by
  apply Bool.eq_iff_iff.2
  unfold checkAllsBwd
  simp only [fAll_iff, List.all_eq_true, mem_allsMapOf, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not]
  constructor
  · intro h ⟨R, c⟩ hp
    by_cases hR : R.flip ∈ L
    · have hp' : (R.flip.flip, c) ∈ ps := by rwa [SRI.RoleT.flip_flip]
      exact Or.inr (h R.flip hR c hp')
    · exact Or.inl hR
  · intro h R hR c hp
    have hR' : R.flip.flip ∈ L := by rwa [SRI.RoleT.flip_flip]
    exact (h (R.flip, c) hp).resolve_left (not_not.2 hR')

def getAllsM (ix : SIx n m) (allMA : Array (Std.HashMap (RoleT (Fin m)) (List (Fin n)))) (c : Fin h.k) :
    Std.HashMap (RoleT (Fin m)) (List (Fin n)) :=
  allMA[c.val]?.getD (allsMapOf (allsOf ix (h.tyF c)))

theorem getAllsM_eq (ix : SIx n m) (c : Fin h.k) :
    getAllsM h ix (Array.ofFn fun b : Fin h.k => allsMapOf (allsOf ix (h.tyF b))) c =
      allsMapOf (allsOf ix (h.tyF c)) := by
  unfold getAllsM
  rw [Array.getElem?_ofFn]
  simp [c.isLt]

def addNbrC {n m : Nat} (L : Finset (RoleT (Fin m))) (c : Fin n)
    (mp : Std.HashMap (Fin n) (List (Finset (RoleT (Fin m))))) :
    Std.HashMap (Fin n) (List (Finset (RoleT (Fin m)))) :=
  mp.insert c (L :: (mp[c]?).getD [])

theorem foldr_addNbrC {n m : Nat} (L : Finset (RoleT (Fin m)))
    (mp : Std.HashMap (Fin n) (List (Finset (RoleT (Fin m))))) (c : Fin n) :
    ∀ (l : List (Fin n)), l.Nodup →
      (((l.foldr (addNbrC L) mp)[c]?).getD []) =
        if c ∈ l then L :: (mp[c]?).getD [] else (mp[c]?).getD []
  | [], _ => by simp
  | a :: l, hnd => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hnd
    simp only [List.foldr_cons, addNbrC, Std.HashMap.getElem?_insert, List.mem_cons]
    by_cases h : a = c
    · subst h
      simp [ha, foldr_addNbrC L mp a l hl]
    · have hb : (c == a) = false := beq_false_of_ne (Ne.symm h)
      have hca : c ≠ a := Ne.symm h
      simp [h, hb, hca, foldr_addNbrC L mp c l hl]

def addNbr {n m : Nat} (e : QNbr n m)
    (mp : Std.HashMap (Fin n) (List (Finset (RoleT (Fin m))))) :
    Std.HashMap (Fin n) (List (Finset (RoleT (Fin m)))) :=
  (SRI.Proc.toL e.2).reverse.foldl (fun m c => addNbrC e.1 c m) mp

theorem addNbr_getD {n m : Nat} (e : QNbr n m)
    (mp : Std.HashMap (Fin n) (List (Finset (RoleT (Fin m))))) (c : Fin n) :
    (((addNbr e mp)[c]?).getD []) =
      if c ∈ e.2 then e.1 :: (mp[c]?).getD [] else (mp[c]?).getD [] := by
  unfold addNbr
  rw [← List.foldr_eq_foldl_reverse, foldr_addNbrC e.1 mp c (SRI.Proc.toL e.2)
    ((SRI.Proc.toL_sorted e.2).imp ne_of_lt)]
  simp only [SRI.Proc.mem_toL]

def nbrsByC {n m : Nat} (N : List (QNbr n m)) :
    Std.HashMap (Fin n) (List (Finset (RoleT (Fin m)))) :=
  N.reverse.foldl (fun mp e => addNbr e mp) ∅

theorem foldr_addNbr {n m : Nat} (c : Fin n) :
    ∀ (N : List (QNbr n m)),
      (((N.foldr addNbr ∅)[c]?).getD []) =
        (N.filter fun e => decide (c ∈ e.2)).map (·.1)
  | [] => by simp
  | e :: N => by
    simp only [List.foldr_cons, addNbr_getD, List.filter_cons, foldr_addNbr c N]
    by_cases h : c ∈ e.2 <;> simp [h]

theorem cnt_nbrsByC {n m : Nat} (N : List (QNbr n m)) (R : RoleT (Fin m)) (c : Fin n) :
    (((nbrsByC N)[c]?).getD []).countP (fun L => decide (R ∈ L)) = cnt N R c := by
  unfold nbrsByC
  rw [← List.foldr_eq_foldl_reverse, foldr_addNbr, List.countP_map, List.countP_filter]
  unfold cnt
  refine List.countP_congr fun e _ => ?_
  simp only [Function.comp_apply, Bool.decide_and, Bool.and_comm]

def smallTy {α : Type} (s : Finset α) : Bool :=
  Quot.liftOn s.val (fun l => (l.drop 512).isEmpty) fun l l' (h : l.Perm l') => by
    apply Bool.eq_iff_iff.2
    rw [List.isEmpty_iff, List.isEmpty_iff, List.drop_eq_nil_iff, List.drop_eq_nil_iff, h.length_eq]

def checkLowsUpps {n m : Nat} (lows upps : List (Nat × RoleT (Fin m) × Fin n))
    (N_M : List (Finset (RoleT (Fin m)) × MemS n)) (N : Unit → List (QNbr n m)) : Bool × Bool :=
  if 64 < lows.length + upps.length && 64 < N_M.length && (N ()).all (fun e => smallTy e.2) then
    let byC := nbrsByC (N ())
    (lows.all (fun q => atLeastP q.1 ((byC[q.2.2]?).getD []) (fun L => decide (q.2.1 ∈ L))),
     upps.all (fun q => decide ((((byC[q.2.2]?).getD []).countP fun L => decide (q.2.1 ∈ L)) ≤ q.1)))
  else
    (lows.all (fun q => atLeastP q.1 N_M (fun e => e.2.f q.2.2 && decide (q.2.1 ∈ e.1))),
     upps.all (fun q => decide (N_M.countP (fun e => e.2.f q.2.2 && decide (q.2.1 ∈ e.1)) ≤ q.1)))

theorem checkLowsUpps_eq {n m : Nat} (lows upps : List (Nat × RoleT (Fin m) × Fin n))
    (N : List (QNbr n m)) :
    checkLowsUpps lows upps (N.map fun e => (e.1, memTS e.2)) (fun _ => N) =
      (lows.all (fun q => decide (q.1 ≤ cnt N q.2.1 q.2.2)),
       upps.all (fun q => decide (cnt N q.2.1 q.2.2 ≤ q.1))) := by
  unfold checkLowsUpps
  simp only [atLeastP_eq, cnt_nbrsByC, cnt_map_memTS, ite_self]

def starCoreF (ix : SIx n m) (memA : Array (MemBox n))
    (allMA : Array (Std.HashMap (RoleT (Fin m)) (List (Fin n))))
    (A : Array (List (Fin h.k × Finset (RoleT (Fin m)))))
    (kb : Array (List (QNbr n m))) (b : Fin h.k) : Bool :=
  let t := h.tyF b
  let MS := getMem h memA b
  let M := MS.f
  let allsM := getAllsM h ix allMA b
  let lows := lowsOf ix t
  let upps := uppsOf ix t
  let cEdges := (merged (getL A b.val)).filter fun e => decide (e.2 ≠ ∅)
  let kEdges := getL kb b.val
  let N_M : List (Finset (RoleT (Fin m)) × MemS n) :=
    (cEdges.map fun e => (e.2, getMem h memA e.1)) ++ (kEdges.map fun e => (e.1, memTS e.2))
  let lu := if lows.isEmpty && upps.isEmpty then (true, true)
    else checkLowsUpps lows upps N_M (fun _ => (cEdges.map fun e => (e.2, h.tyF e.1)) ++ kEdges)
  closedBF ix M t &&
  (cEdges.all (fun e => upB ix e.2 && checkAllsBwd (getAllsM h ix allMA e.1) e.2 M) &&
   kEdges.all (fun e => upB ix e.1 &&
    (allsOf ix e.2).all (fun p => !decide (p.1.flip ∈ e.1) || M p.2))) &&
  N_M.all (fun e => checkAllsFwd allsM e.1 e.2.f) && lu.1 && lu.2

theorem if_isEmpty_pair {α β : Type} (l1 : List α) (l2 : List β) (p1 : α → Bool) (p2 : β → Bool) :
    (if l1.isEmpty && l2.isEmpty then (true, true) else (l1.all p1, l2.all p2)) =
      (l1.all p1, l2.all p2) := by
  cases l1 <;> cases l2 <;> rfl

theorem starCoreF_eq (ix : SIx n m)
    (A : Array (List (Fin h.k × Finset (RoleT (Fin m)))))
    (kb : Array (List (QNbr n m))) (b : Fin h.k) :
    starCoreF h ix (Array.ofFn fun c : Fin h.k => mkMemBox (h.tyF c))
      (Array.ofFn fun c : Fin h.k => allsMapOf (allsOf ix (h.tyF c))) A kb b =
    starF ix (h.tyF b) (h.starL A b ++ getL kb b.val) := by
  unfold starCoreF starF
  dsimp only
  simp only [getMem_eq, getAllsM_eq, closedBF_eq, checkAllsBwd_eq, checkAllsFwd_eq]
  set cEdges := (merged (getL A b.val)).filter fun e => decide (e.2 ≠ ∅)
  set kEdges := getL kb b.val
  set N := h.starL A b ++ kEdges
  have hN0 : (fun _ : Unit => (cEdges.map fun e => (e.2, h.tyF e.1)) ++ kEdges) = (fun _ => N) := rfl
  have hNM : (cEdges.map fun e => (e.2, memTS (h.tyF e.1))) ++ (kEdges.map fun e => (e.1, memTS e.2)) =
      N.map fun e => (e.1, memTS e.2) := by
    simp [N, HintS.starL, cEdges, List.map_append, List.map_map, Function.comp_def]
  rw [hN0, hNM, checkLowsUpps_eq, if_isEmpty_pair]
  dsimp only
  simp only [all_lowsOf, all_uppsOf]
  have h1 : (N.map fun e => (e.1, memTS e.2)).all (fun e =>
        (allsOf ix (h.tyF b)).all fun p => !decide (p.1 ∈ e.1) || e.2.f p.2) =
      N.all (fun e => edgeAll ix (memTS e.2) (h.tyF b) e) := by
    rw [List.all_map]
    refine List.all_congr rfl fun e => ?_
    simp only [Function.comp_apply, all_allsOf, edgeAll]
  rw [h1]
  simp only [all_allsOf]
  have h2 : (cEdges.all (fun e => upB ix e.2 &&
        fAll (h.tyF e.1) (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1.flip ∈ e.2) || (memTS (h.tyF b)).f p.2)) &&
      kEdges.all (fun e => upB ix e.1 &&
        fAll e.2 (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1.flip ∈ e.1) || (memTS (h.tyF b)).f p.2))) =
      N.all (fun e => upB ix e.1 &&
        fAll e.2 (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1.flip ∈ e.1) || (memTS (h.tyF b)).f p.2)) := by
    simp [N, HintS.starL, cEdges, List.all_append, List.all_map, Function.comp_def]
  rw [h2]
  unfold edgeB
  apply Bool.eq_iff_iff.2
  simp only [Bool.and_eq_true, List.all_eq_true]
  exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨⟨⟨h1, fun e he => ⟨(h2 e he).1, h3 e he, (h2 e he).2⟩⟩, h4⟩, h5⟩,
         fun ⟨⟨⟨h1, h2⟩, h4⟩, h5⟩ => ⟨⟨⟨⟨h1, fun e he => ⟨(h2 e he).1, (h2 e he).2.2⟩⟩, fun e he => (h2 e he).2.1⟩, h4⟩, h5⟩⟩

def coreBF (ix : SIx n m) (N : List (Fin n)) : Bool :=
  let A := h.adj
  let kb := h.kidIdx
  let memA := Array.ofFn fun c : Fin h.k => mkMemBox (h.tyF c)
  let allMA := Array.ofFn fun c : Fin h.k => allsMapOf (allsOf ix (h.tyF c))
  decide (0 < h.k) && nomOKS h N &&
    (List.finRange h.k).all fun b => starCoreF h ix memA allMA A kb b

@[csimp] theorem coreB_eq_F : @coreB = @coreBF := by
  funext n m h ix N
  unfold coreB coreBF
  dsimp only
  congr 1
  refine List.all_congr rfl fun b => (starCoreF_eq h ix h.adj h.kidIdx b).symm

theorem coreB_eq (O : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) :
    coreB h (mkSIx O) N = decide (0 < h.toN.k ∧ coreOKN N h.toN.ty h.toN.lab ∧
      ∀ b, StarOK O (h.toN.ty b) (SRIQ.Proc.nbrsL h.toN.ty h.toN.lab b ++ h.toN.kids b)) := by
  apply Bool.eq_iff_iff.2
  unfold coreB coreOKN
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies, starF_iff, nomOKS_iff]
  have hstar : ∀ b, StarOK O (h.tyF b) (h.starL h.adj b ++ getL h.kidIdx b.val) ↔
      StarOK O (h.toN.ty b) (SRIQ.Proc.nbrsL h.toN.ty h.toN.lab b ++ h.toN.kids b) := fun b =>
    ⟨fun hs => SRIQN.starOK_perm' ((starL_perm h b).append (kidIdx_perm h b)) hs,
     fun hs => SRIQN.starOK_perm' ((starL_perm h b).append (kidIdx_perm h b)).symm hs⟩
  simp only [hstar]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, ⟨fun b c => toN_symm h b c, h2⟩, h3⟩
  · rintro ⟨h1, ⟨-, h2⟩, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-- A certificate row, through the index. -/
def recB (ix : SIx n m) (nm : Array Bool) (G : List (NRec n m h.k)) (r : RecS n m h.k) : Bool :=
  !fAny r.ty (memM nm) &&
  (match r.par with
    | .inr (c, _) => decide (labOf r.ce c = ∅)
    | .inl _ => true) &&
  (merged r.ce).all (fun e => !countedB ix (h.tyF e.1) (flipL e.2) r.ty) &&
  starF ix r.ty ((parentE h.tyF r.par :: h.ceL r) ++ r.kids) &&
  r.kids.all fun x => memB G (childRecN r.ty x)

/-- **The certificate check**, through the index. -/
def certB (ix : SIx n m) (N : List (Fin n)) : Bool :=
  let nm := maskL n N
  let G := h.recs.map fun r => ((r.ty, r.par) : NRec n m h.k)
  h.kids.all (fun e => memB G (anchorRec e.1 e.2)) && h.recs.all (recB h ix nm G)

theorem ceL_perm (r : RecS n m h.k) : (h.ceL r).Perm (cEntriesL h.tyF (labOf r.ce)) :=
  merged_perm _ _ _ fun _ => rfl

theorem recB_iff (O : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) (G : List (NRec n m h.k))
    (r : RecS n m h.k) :
    recB h (mkSIx O) (maskL n N) G r = true ↔ recOK O N h.toN.ty G r.toN := by
  unfold recB recOK ceOK
  simp only [RecS.toN, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, starF_iff, memL_iff,
    memB_iff]
  have hty : h.toN.ty = h.tyF := rfl
  rw [hty]
  have h1 : fAny r.ty (memM (maskL n N)) = false ↔ ∀ a ∈ N, a ∉ r.ty := by
    rw [← Bool.not_eq_true, fAny_iff]
    simp only [memM_maskL, decide_eq_true_eq, not_exists, not_and]
    exact ⟨fun h a ha hr => h a hr ha, fun h a hr ha => h a ha hr⟩
  have h2 : (match r.par with
      | .inr (c, _) => decide (labOf r.ce c = ∅)
      | .inl _ => true) = true ↔ ∀ c, (∃ L, r.par = .inr (c, L)) → labOf r.ce c = ∅ := by
    rcases hp : r.par with p | ⟨c, L⟩
    · simp
    · simp only [decide_eq_true_eq, Sum.inr.injEq, Prod.mk.injEq]
      constructor
      · rintro h c' ⟨L', rfl, rfl⟩; exact h
      · intro h; exact h c ⟨L, rfl, rfl⟩
  have h3 : (∀ e ∈ merged r.ce, countedB (mkSIx O) (h.tyF e.1) (flipL e.2) r.ty = false) ↔
      ∀ d, ¬ Counted O (h.tyF d) (flipL (labOf r.ce d)) r.ty := by
    simp only [← Bool.not_eq_true, countedB_iff]
    constructor
    · intro hc d hd
      by_cases hk : ∃ e ∈ merged r.ce, e.1 = d
      · obtain ⟨e, he, rfl⟩ := hk
        rw [← merged_lab he] at hd
        exact hc e he hd
      · have he : labOf r.ce d = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun x hx => hk ?_
          rw [mem_labOf, ← merged_mem] at hx
          obtain ⟨e, he, hk', -⟩ := hx
          exact ⟨e, he, hk'⟩
        rw [he, SRIQN.flipL_empty] at hd
        obtain ⟨_, _, _, _, _, _, hR, _⟩ := hd
        exact Finset.notMem_empty _ hR
    · intro hc e he hd
      rw [merged_lab he] at hd
      exact hc e.1 hd
  have h4 : StarOK O r.ty ((parentE h.tyF r.par :: h.ceL r) ++ r.kids) ↔
      StarOK O r.ty ((parentE h.tyF r.par :: cEntriesL h.tyF (labOf r.ce)) ++ r.kids) :=
    ⟨fun hs => SRIQN.starOK_perm' (((ceL_perm h r).cons _).append_right _) hs,
     fun hs => SRIQN.starOK_perm' (((ceL_perm h r).cons _).append_right _).symm hs⟩
  rw [h1, h2, h3, h4]
  simp only [and_assoc]
  rfl

theorem certB_eq (O : SRIQ.Ontology (Fin n) (Fin m)) (N : List (Fin n)) :
    certB h (mkSIx O) N = decide (CertOK O N h.toN) := by
  apply Bool.eq_iff_iff.2
  unfold certB CertOK
  have hG : h.toN.recs.map Prod.fst = h.recs.map fun r => ((r.ty, r.par) : NRec n m h.k) := by
    simp [HintS.toN, RecS.toN, Function.comp_def]
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hG, memL_iff, memB_iff]
  refine and_congr ?_ ?_
  · constructor
    · intro hk b e he
      simp only [HintS.toN, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
      obtain ⟨x, ⟨hx, rfl⟩, rfl⟩ := he
      exact hk x hx
    · intro hk x hx
      have hm : x.2 ∈ h.toN.kids x.1 := by
        simp only [HintS.toN, List.mem_map, List.mem_filter, decide_eq_true_eq]
        exact ⟨x, ⟨hx, rfl⟩, rfl⟩
      exact hk x.1 x.2 hm
  · have hr : h.toN.recs = h.recs.map RecS.toN := rfl
    rw [hr]
    constructor
    · intro hk e he
      obtain ⟨r, hr', rfl⟩ := List.mem_map.1 he
      exact (recB_iff h O N _ r).1 (hk r hr')
    · intro hk r hr'
      exact (recB_iff h O N _ r).2 (hk _ (List.mem_map_of_mem hr'))

theorem noKids_eq : (List.finRange h.k).all (fun b => (h.toN.kids b).isEmpty) = h.kids.isEmpty := by
  apply Bool.eq_iff_iff.2
  simp only [List.all_eq_true, List.mem_finRange, true_implies, List.isEmpty_iff, HintS.toN,
    List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  constructor
  · intro hk
    cases hl : h.kids with
    | nil => rfl
    | cons x l => exact absurd rfl (hk x.1 x (by rw [hl]; exact List.mem_cons_self))
  · intro hk b x hx
    rw [hk] at hx
    simp at hx

/-- **The hint check of `checkRedN` over a sparse hint.** -/
def checkRedS (A : SRIQ.Ontology (Fin n) (Fin m)) (ok : Finset (Fin n) → Bool) (N : List (Fin n)) :
    Bool :=
  let ix := mkSIx A
  coreB h ix N && (List.finRange h.k).all (fun b => ok (h.tyF b)) &&
    (h.kids.isEmpty || (h.recs.all (fun e => ok e.ty) && certB h ix N))

/-- **The sparse check is the dense check on the denoted hint.** -/
theorem checkRedS_eq (A : SRIQ.Ontology (Fin n) (Fin m)) (ok : Finset (Fin n) → Bool)
    (N : List (Fin n)) : checkRedS h A ok N = Proc.checkRedN A ok N h.toN := by
  unfold checkRedS Proc.checkRedN
  dsimp only
  rw [coreB_eq, certB_eq, ← noKids_eq h]
  have : (h.toN.recs.all fun e => ok e.1.1) = h.recs.all fun e => ok e.ty := by
    simp [HintS.toN, RecS.toN, List.all_map, Function.comp_def]
  rw [this]
  rfl

/-- Loops at nominal elements, from the edge lists. -/
def loopOKS (N : List (Fin n)) : Bool :=
  let nm := maskL n N
  let A := h.adj
  (List.finRange h.k).all fun c => decide (labOf (getL A c.val) c = ∅) || fAny (h.tyF c) (memM nm)

theorem loopOKS_eq (N : List (Fin n)) : loopOKS h N = Proc.loopOKH N h.toN := by
  unfold loopOKS Proc.loopOKH
  simp only [labOf_adj]
  congr 1
  funext c
  congr 1
  apply Bool.eq_iff_iff.2
  rw [fAny_iff, List.any_eq_true]
  simp only [memM_maskL, decide_eq_true_eq]
  exact ⟨fun ⟨a, h1, h2⟩ => ⟨a, h2, h1⟩, fun ⟨a, h1, h2⟩ => ⟨a, h2, h1⟩⟩

end Checks

/-! ## The part loops over a sparse hint -/

section Parts

open ContextCalculus.SRIQD (partsOf toPart partCard)

variable {Val K : Type} [DecidableEq K] {q s p : Nat}

/-- `hintPartsN` over a sparse hint. -/
def hintPartsS (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let A := SRIQD.objPart Db
  let N := dnoms D
  let ix := mkSIx A
  let noKids := h.kids.isEmpty
  (coreB h ix N && (noKids || certB h ix N)) &&
  (partsOf size s (cells.filter sp)).any fun x =>
    let ok := SRIQD.Proc.dataSatB (dataOnly Db) (partCard cells size sp E (toPart s x))
    (List.finRange h.k).all (fun b => ok (h.tyF b)) && (noKids || h.recs.all (fun e => ok e.ty))

theorem hintPartsS_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) :
    hintPartsS O cells size sp E h = hintPartsN O cells size sp E h.toN := by
  rw [hintPartsN_eq_F]
  unfold hintPartsS hintPartsNF
  dsimp only
  simp only [coreB_eq, certB_eq, ← noKids_eq h, dataSatB_dataOnly]
  have : ∀ ok : Finset (Fin (n + Proc.encKD O)) → Bool,
      (h.toN.recs.all fun e => ok e.1.1) = h.recs.all fun e => ok e.ty := fun ok => by
    simp [HintS.toN, RecS.toN, List.all_map, Function.comp_def]
  simp only [this]
  rfl

/-- `hintPartsNL` over a sparse hint. -/
def hintPartsNLS (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  loopOKS h (dnoms (Proc.encTransDN O)) && hintPartsS O cells size sp E h

theorem hintPartsNLS_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) :
    hintPartsNLS O cells size sp E h = hintPartsNL O cells size sp E h.toN := by
  rw [hintPartsNL_eq_F]
  unfold hintPartsNLS hintPartsNLF
  rw [loopOKS_eq, hintPartsS_eq, hintPartsN_eq_F]

/-! ## A data part named by the hint (stage H2, R6) -/

/-- The part a hint names: the count of each group in each split cell
(the cells by their position in `sc`, the groups by their position in
`allG s`); absent lines count zero. -/
def namedPart (sc : List K) (G : Nat) (l : List (Nat × Nat × Nat)) : List (K × List Nat) :=
  sc.zipIdx.map fun p => (p.1, (List.range G).map fun g =>
    ((l.filter fun e => e.1 == p.2 && e.2.1 == g).map (·.2.2)).sum)

def sumPartMap (l : List (Nat × Nat × Nat)) : Std.HashMap (Nat × Nat) Nat :=
  l.reverse.foldl (fun (m : Std.HashMap (Nat × Nat) Nat) e =>
    m.insert (e.1, e.2.1) (e.2.2 + (m[(e.1, e.2.1)]?).getD 0)) ∅

theorem sumPartMap_foldr (i g : Nat) :
    ∀ (l : List (Nat × Nat × Nat)),
      ((l.foldr (fun e (m : Std.HashMap (Nat × Nat) Nat) =>
        m.insert (e.1, e.2.1) (e.2.2 + (m[(e.1, e.2.1)]?).getD 0)) ∅)[(i, g)]?).getD 0 =
        ((l.filter fun e => e.1 == i && e.2.1 == g).map (·.2.2)).sum
  | [] => by simp
  | e :: l => by
    simp only [List.foldr_cons, Std.HashMap.getElem?_insert, List.filter_cons]
    by_cases h1 : e.1 = i
    · by_cases h2 : e.2.1 = g
      · subst h1; subst h2
        simp [sumPartMap_foldr]
      · simp [h1, h2, sumPartMap_foldr i g l]
    · simp [h1, sumPartMap_foldr i g l]

def namedPartF (sc : List K) (G : Nat) (l : List (Nat × Nat × Nat)) : List (K × List Nat) :=
  let mp := sumPartMap l
  sc.zipIdx.map fun p => (p.1, (List.range G).map fun g => (mp[(p.2, g)]?).getD 0)

@[csimp] theorem namedPart_eq_F : @namedPart = @namedPartF := by
  funext K sc G l
  unfold namedPart namedPartF sumPartMap
  simp only [← List.foldr_eq_foldl_reverse, sumPartMap_foldr]

/-- The named part is a part: one count list per split cell, of the right
length and sum. -/
def validPartB (size : K → Option Nat) (s : Nat) (sc : List K) (x : List (K × List Nat)) : Bool :=
  decide (x.map Prod.fst = sc) &&
    x.all fun p => p.2.length == (ContextCalculus.SRIQD.allG s).length && p.2.sum == (size p.1).getD 0

theorem mem_of_validPartB {size : K → Option Nat} {sc : List K} {x : List (K × List Nat)}
    (h : validPartB size s sc x = true) : x ∈ partsOf size s sc := by
  unfold validPartB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  exact ContextCalculus.SRIQD.mem_partsOf.2 ⟨h.1, fun p hp =>
    ContextCalculus.SRIQD.mem_comps.2 ⟨(h.2 p hp).1, (h.2 p hp).2⟩⟩

/-! ## Data stars given by the hint (stage H2, R6 per element) -/

/-- A given data star of a type, checked directly: no more entries than the
bound, each a possible entry, and the star conditions. -/
def starGivenB (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat)
    (t : Finset (Fin n)) (Dn : List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))) : Bool :=
  decide (Dn.length ≤ SRIQD.dbnd O) && Dn.all (fun e => decide (SRIQD.Proc.dcandOK O card t e)) &&
    decide (SRIQD.DOK O card t Dn)

theorem dataSatB_of_starGivenB {O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {card : Finset (Fin q) → Option Nat} {t : Finset (Fin n)}
    {Dn : List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))} (h : starGivenB O card t Dn = true) :
    SRIQD.Proc.dataSatB O card t = true := by
  unfold starGivenB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold SRIQD.Proc.dataSatB
  rw [decide_eq_true_iff]
  refine ⟨Dn, (SRIQ.Proc.mem_listsUpTo _ _).2 ⟨h1, fun e he => ?_⟩, h3⟩
  show e ∈ (SRIQD.Proc.dcands O card t)
  unfold SRIQD.Proc.dcands
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h2 e he⟩

/-- The given data stars by element: `none` for an element without one,
`some l` with `none` in `l` for an entry with an index out of range. -/
def starsOf {p q : Nat} (h : HintS n m) : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))) :=
  let fins (k : Nat) (l : List Nat) : Option (List (Fin k)) := l.mapM fun x => if hx : x < k then some ⟨x, hx⟩ else none
  let base : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))) :=
    h.dgiven.foldl (fun A b => if b < h.k then A.setIfInBounds b (some []) else A) (Array.replicate h.k none)
  h.dstar.foldl (fun A e =>
    let entry := (fins p e.2.1).bind fun ps => (fins q e.2.2).map fun as => (ps.toFinset, as.toFinset)
    A.modify e.1 fun o => some (entry :: o.getD [])) base

/-- The data-star test of a core element: its given star, or the search. -/
def okOf {p q : Nat} (Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) (card : Finset (Fin q) → Option Nat)
    (h : HintS n m) (stars : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))))
    (b : Fin h.k) : Bool :=
  match (stars[b.val]?).getD none with
  | some l => if l.all Option.isSome then starGivenB Db card (h.tyF b) (l.filterMap id) else false
  | none => SRIQD.Proc.dataSatB Db card (h.tyF b)

theorem okOf_imp {p q : Nat} {Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)}
    {card : Finset (Fin q) → Option Nat} {h : HintS n m} {stars} {b : Fin h.k}
    (hb : okOf Db card h stars b = true) : SRIQD.Proc.dataSatB Db card (h.tyF b) = true := by
  unfold okOf at hb
  split at hb
  · split_ifs at hb
    exact dataSatB_of_starGivenB hb
  · exact hb

/-- The values of `card` on `L` (stage H4: the oracle of a part is a sum
over the split cells, and the star tests ask it once per entry). -/
def memoTab {q : Nat} (card : Finset (Fin q) → Option Nat) (L : List (Finset (Fin q))) :
    List (Finset (Fin q) × Option Nat) :=
  L.map fun τ => (τ, card τ)

/-- `card` read from a table first. -/
def lookCard {q : Nat} (card : Finset (Fin q) → Option Nat) (tab : List (Finset (Fin q) × Option Nat))
    (τ : Finset (Fin q)) : Option Nat :=
  match tab.lookup τ with
  | some v => v
  | none => card τ

/-- `card` with its values on `L` computed once. -/
def memoCard {q : Nat} (card : Finset (Fin q) → Option Nat) (L : List (Finset (Fin q))) :
    Finset (Fin q) → Option Nat :=
  lookCard card (memoTab card L)

theorem lookup_map_self' {α β : Type} [DecidableEq α] (g : α → β) :
    ∀ (L : List α) (a : α) (v : β), (L.map fun x => (x, g x)).lookup a = some v → v = g a
  | [], _, _, h => by simp at h
  | x :: L, a, v, h => by
    simp only [List.map_cons, List.lookup_cons] at h
    split at h
    next he =>
      cases h
      rw [beq_iff_eq] at he
      rw [he]
    next => exact lookup_map_self' g L a v h

@[simp] theorem memoCard_eq {q : Nat} (card : Finset (Fin q) → Option Nat) (L : List (Finset (Fin q))) :
    memoCard card L = card := by
  funext τ
  unfold memoCard lookCard memoTab
  split
  next v hv => exact lookup_map_self' card L τ v hv
  next => rfl

/-- The cells to split, as a table (stage H4: `splitCell` recomputes the
value types of every pair for every cell it is asked about). -/
def splitTab {K : Type} [DecidableEq K] {q s : Nat} (cells : List K) (size : K → Option Nat)
    (L : Nat) (E : Fin q → K → (Fin s → Bool) → Bool) : List (K × Bool) :=
  let big := ((SRIQD.pairs cells s).filter fun cg => !SRIQD.small size L cg.1).map fun cg =>
    SRI.Proc.toL (SRIQD.vtc E cg.1 cg.2)
  let bigS : Std.HashSet (List (Fin q)) := Std.HashSet.ofList big
  cells.map fun c => (c, SRIQD.small size L c &&
    !((SRIQD.allG s).all fun g => bigS.contains (SRI.Proc.toL (SRIQD.vtc E c g))))

/-- A predicate read from a table first. -/
def lookSplit {K : Type} [DecidableEq K] (tab : List (K × Bool)) (sp : K → Bool) (c : K) : Bool :=
  match tab.lookup c with
  | some b => b
  | none => sp c

theorem splitTab_lookup {K : Type} [DecidableEq K] {q s : Nat} (cells : List K) (size : K → Option Nat)
    (L : Nat) (E : Fin q → K → (Fin s → Bool) → Bool) (c : K) (b : Bool)
    (h : (splitTab cells size L E).lookup c = some b) : b = SRIQD.splitCell cells size L E c := by
  let big := ((SRIQD.pairs cells s).filter fun cg => !SRIQD.small size L cg.1).map fun cg =>
    SRI.Proc.toL (SRIQD.vtc E cg.1 cg.2)
  let bigS : Std.HashSet (List (Fin q)) := Std.HashSet.ofList big
  have key : ∀ (l : List K), (l.map fun c => (c, SRIQD.small size L c &&
      !((SRIQD.allG s).all fun g => bigS.contains (SRI.Proc.toL (SRIQD.vtc E c g))))).lookup c = some b →
      b = (SRIQD.small size L c && !((SRIQD.allG s).all fun g =>
        bigS.contains (SRI.Proc.toL (SRIQD.vtc E c g)))) := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons x l ih =>
      simp only [List.map_cons, List.lookup_cons] at hl
      split at hl
      next he => cases hl; rw [beq_iff_eq] at he; rw [he]
      next => exact ih hl
  rw [key cells h]
  unfold SRIQD.splitCell SRIQD.covered
  congr 2
  apply congrArg
  funext g
  apply Bool.eq_iff_iff.2
  simp only [bigS, big, Std.HashSet.contains_ofList, List.elem_eq_mem, List.mem_map, List.mem_filter,
    SRIQD.mem_pairs, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  constructor
  · rintro ⟨⟨c', g'⟩, ⟨hc, hs⟩, he⟩
    exact ⟨c', hc, by simpa using hs, g', SRIQD.mem_allG g', SRI.Proc.toL_inj he⟩
  · rintro ⟨c', hc, hs, g', -, he⟩
    exact ⟨(c', g'), ⟨hc, by simpa using hs⟩, congrArg SRI.Proc.toL he⟩

/-- **The table changes nothing.** -/
theorem lookSplit_eq {K : Type} [DecidableEq K] {q s : Nat} (cells : List K) (size : K → Option Nat)
    (L : Nat) (E : Fin q → K → (Fin s → Bool) → Bool) :
    lookSplit (splitTab cells size L E) (SRIQD.splitCell cells size L E) =
      SRIQD.splitCell cells size L E := by
  funext c
  unfold lookSplit
  split
  next b hb => exact splitTab_lookup cells size L E c b hb
  next => rfl

/-- First-occurrence hash map of a key-value list. -/
def mapOfL {K V : Type} [DecidableEq K] [Hashable K] (l : List (K × V)) : Std.HashMap K V :=
  l.reverse.foldl (fun (m : Std.HashMap K V) e => m.insert e.1 e.2) ∅

theorem foldr_insert_lookup {K V : Type} [DecidableEq K] [Hashable K] (c : K) :
    ∀ (l : List (K × V)),
      ((l.foldr (fun e (m : Std.HashMap K V) => m.insert e.1 e.2) ∅)[c]?) = l.lookup c
  | [] => by simp
  | (k, v) :: l => by
    simp only [List.foldr_cons, Std.HashMap.getElem?_insert, List.lookup_cons]
    by_cases h : k = c
    · subst h; simp
    · have hb : (c == k) = false := beq_false_of_ne (Ne.symm h)
      simp [h, hb, foldr_insert_lookup c l]

theorem mapOfL_get {K V : Type} [DecidableEq K] [Hashable K] (l : List (K × V)) (c : K) :
    (mapOfL l)[c]? = l.lookup c := by
  unfold mapOfL
  rw [← List.foldr_eq_foldl_reverse]
  exact foldr_insert_lookup c l

def useLookSplitH {K : Type} [DecidableEq K] [Hashable K] (mp : Std.HashMap K Bool)
    (sp : K → Bool) (c : K) : Bool :=
  match mp[c]? with
  | some b => b
  | none => sp c

structure LookSplitHS (K : Type) where
  f : K → Bool

/-- `lookSplit` backed by a `Std.HashMap`, wrapped in a structure so the compiler does not eta-expand `mapOfL` into each lookup. -/
def lookSplitHS {K : Type} [DecidableEq K] [Hashable K] (tab : List (K × Bool)) (sp : K → Bool) :
    LookSplitHS K :=
  let mp := mapOfL tab
  ⟨useLookSplitH mp sp⟩

@[simp] theorem lookSplitHS_f {K : Type} [DecidableEq K] [Hashable K]
    (tab : List (K × Bool)) (sp : K → Bool) :
    (lookSplitHS tab sp).f = lookSplit tab sp := by
  funext c
  simp only [lookSplitHS, useLookSplitH, lookSplit, mapOfL_get]

theorem lookSplitHS_eq {K : Type} [DecidableEq K] [Hashable K] {q s : Nat}
    (cells : List K) (size : K → Option Nat) (L : Nat) (E : Fin q → K → (Fin s → Bool) → Bool) :
    (lookSplitHS (splitTab cells size L E) (SRIQD.splitCell cells size L E)).f =
      SRIQD.splitCell cells size L E := by
  rw [lookSplitHS_f, lookSplit_eq]

def useToPartH {K : Type} [DecidableEq K] [Hashable K] {s : Nat}
    (mp : Std.HashMap K (List Nat)) (gs : List (Fin s → Bool)) (c : K) (g : Fin s → Bool) : Nat :=
  ((mp[c]?).getD []).getD (gs.idxOf g) 0

structure ToPartHS (K : Type) (s : Nat) where
  f : K → (Fin s → Bool) → Nat

/-- `toPart` backed by a `Std.HashMap`, wrapped in a structure so `mapOfL` is computed once. -/
def toPartHS {K : Type} [DecidableEq K] [Hashable K] (s : Nat) (a : List (K × List Nat)) :
    ToPartHS K s :=
  let mp := mapOfL a
  let gs := SRIQD.allG s
  ⟨useToPartH mp gs⟩

@[simp] theorem toPartHS_f {K : Type} [DecidableEq K] [Hashable K] (s : Nat) (a : List (K × List Nat)) :
    (toPartHS s a).f = toPart s a := by
  funext c g
  simp only [toPartHS, useToPartH, toPart, mapOfL_get]

/-- `splitTab` computed with a fast `vtcF` function. -/
def splitTabV {K : Type} {q s : Nat} (cells : List K) (size : K → Option Nat)
    (L : Nat) (vtcF : K → (Fin s → Bool) → Finset (Fin q)) : List (K × Bool) :=
  let big := ((SRIQD.pairs cells s).filter fun cg => !SRIQD.small size L cg.1).map fun cg =>
    SRI.Proc.toL (vtcF cg.1 cg.2)
  let bigS : Std.HashSet (List (Fin q)) := Std.HashSet.ofList big
  cells.map fun c => (c, SRIQD.small size L c &&
    !((SRIQD.allG s).all fun g => bigS.contains (SRI.Proc.toL (vtcF c g))))

theorem splitTabV_eq {K : Type} [DecidableEq K] {q s : Nat} (cells : List K) (size : K → Option Nat)
    (L : Nat) (E : Fin q → K → (Fin s → Bool) → Bool)
    (vtcF : K → (Fin s → Bool) → Finset (Fin q)) (hvtc : ∀ c g, vtcF c g = SRIQD.vtc E c g) :
    splitTabV cells size L vtcF = splitTab cells size L E := by
  simp only [splitTabV, splitTab, hvtc]

/-- The value type and the bound of every pair of a part (stage H4: the
oracle `partCard` recomputes them for every value type it is asked). -/
def partTab {K : Type} {q s : Nat} (cells : List K) (size : K → Option Nat) (sp : K → Bool)
    (E : Fin q → K → (Fin s → Bool) → Bool) (n : K → (Fin s → Bool) → Nat) :
    List (Finset (Fin q) × Option Nat) :=
  (SRIQD.pairs cells s).map fun cg => (SRIQD.vtc E cg.1 cg.2, SRIQD.pairBound size sp n cg)

/-- `partTab` computed with a fast `vtcF` function. -/
def partTabV {K : Type} {q s : Nat} (cells : List K) (size : K → Option Nat) (sp : K → Bool)
    (vtcF : K → (Fin s → Bool) → Finset (Fin q)) (n : K → (Fin s → Bool) → Nat) :
    List (Finset (Fin q) × Option Nat) :=
  (SRIQD.pairs cells s).map fun cg => (vtcF cg.1 cg.2, SRIQD.pairBound size sp n cg)

theorem partTabV_eq {K : Type} {q s : Nat} (cells : List K) (size : K → Option Nat) (sp : K → Bool)
    (E : Fin q → K → (Fin s → Bool) → Bool)
    (vtcF : K → (Fin s → Bool) → Finset (Fin q)) (hvtc : ∀ c g, vtcF c g = SRIQD.vtc E c g)
    (n : K → (Fin s → Bool) → Nat) :
    partTabV cells size sp vtcF n = partTab cells size sp E n := by
  simp only [partTabV, partTab, hvtc]

/-- The oracle of a part read from its table. -/
def partCardT {q : Nat} (tab : List (Finset (Fin q) × Option Nat)) (τ : Finset (Fin q)) : Option Nat :=
  SRIQD.osum (tab.map fun e => if e.1 = τ then e.2 else some 0)

theorem oaddN_zero_left (x : Option Nat) : SRIQD.oaddN (some 0) x = x := by
  cases x <;> simp [SRIQD.oaddN]

def sumMap {α : Type} [DecidableEq α] [Hashable α] (l : List (α × Option Nat)) :
    Std.HashMap α (Option Nat) :=
  l.reverse.foldl (fun (m : Std.HashMap α (Option Nat)) e =>
    m.insert e.1 (SRIQD.oaddN e.2 ((m[e.1]?).getD (some 0)))) ∅

theorem sumMap_foldr {α : Type} [DecidableEq α] [Hashable α] (k : α) :
    ∀ (l : List (α × Option Nat)),
      ((l.foldr (fun e (m : Std.HashMap α (Option Nat)) =>
        m.insert e.1 (SRIQD.oaddN e.2 ((m[e.1]?).getD (some 0)))) ∅)[k]?).getD (some 0) =
        SRIQD.osum (l.map fun e => if e.1 = k then e.2 else some 0)
  | [] => by simp [SRIQD.osum]
  | e :: l => by
    simp only [List.foldr_cons, Std.HashMap.getElem?_insert, List.map_cons, SRIQD.osum]
    by_cases h : e.1 = k
    · subst h
      have ih := sumMap_foldr e.1 l
      unfold SRIQD.osum at ih
      simp [ih]
    · have ih := sumMap_foldr k l
      unfold SRIQD.osum at ih
      simp [h, ih, oaddN_zero_left]

def usePartCard {q : Nat} {α : Type} [DecidableEq α] [Hashable α] (f : Finset (Fin q) → α)
    (mp : Std.HashMap α (Option Nat)) (τ : Finset (Fin q)) : Option Nat :=
  (mp[f τ]?).getD (some 0)

structure PartCardS (q : Nat) where
  f : Finset (Fin q) → Option Nat

def partCardTS {q : Nat} (tab : List (Finset (Fin q) × Option Nat)) : PartCardS q :=
  let mp := sumMap (tab.map fun e => (SRI.Proc.toL e.1, e.2))
  ⟨usePartCard SRI.Proc.toL mp⟩

@[simp] theorem partCardTS_f {q : Nat} (tab : List (Finset (Fin q) × Option Nat)) :
    (partCardTS tab).f = partCardT tab := by
  funext τ
  unfold partCardT partCardTS usePartCard sumMap
  dsimp only
  rw [← List.foldr_eq_foldl_reverse, sumMap_foldr, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply]
  by_cases h : e.1 = τ
  · subst h; simp
  · have hne : SRI.Proc.toL e.1 ≠ SRI.Proc.toL τ := fun he => h (SRI.Proc.toL_inj he)
    simp [h, hne]

theorem partCardT_eq {K : Type} [DecidableEq K] {q s : Nat} (cells : List K) (size : K → Option Nat)
    (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool) (n : K → (Fin s → Bool) → Nat) :
    partCardT (partTab cells size sp E n) = SRIQD.partCard cells size sp E n := by
  funext τ
  simp only [partCardT, partTab, SRIQD.partCard, List.map_map, Function.comp_def]

/-- Indexed data clauses of an ontology for fast `starGivenB` checking. -/
structure DIx (n p q : Nat) where
  bnd : Nat
  dSub : List (Fin p × Fin p)
  lowBy : Array (List (Nat × Fin p × List (Fin q) × List (Fin q)))
  uppBy : Array (List (Nat × Fin p × List (Fin q) × List (Fin q)))
  allBy : Array (List (Fin p × List (Fin q × Bool)))

def mkDIx (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)) : DIx n p q where
  bnd := SRIQD.dbnd O
  dSub := SRIQD.dSubL O
  lowBy := buildIdx n (fun c => some (c.1.val, c.2)) (SRIQD.dLowerL O)
  uppBy := buildIdx n (fun c => some (c.1.val, c.2)) (SRIQD.dUpperL O)
  allBy := buildIdx n (fun c => some (c.1.val, c.2)) (SRIQD.dAllL O)

theorem mem_dLowBy {O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {a : Fin n}
    {c : Nat × Fin p × List (Fin q) × List (Fin q)} :
    c ∈ getL (mkDIx O).lowBy a.val ↔ (a, c) ∈ SRIQD.dLowerL O := by
  simp only [mkDIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨q', hq, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = q'.1 from (Fin.ext h1).symm]
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_dUppBy {O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {a : Fin n}
    {c : Nat × Fin p × List (Fin q) × List (Fin q)} :
    c ∈ getL (mkDIx O).uppBy a.val ↔ (a, c) ∈ SRIQD.dUpperL O := by
  simp only [mkDIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨q', hq, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = q'.1 from (Fin.ext h1).symm]
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_dAllBy {O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q)} {a : Fin n}
    {c : Fin p × List (Fin q × Bool)} :
    c ∈ getL (mkDIx O).allBy a.val ↔ (a, c) ∈ SRIQD.dAllL O := by
  simp only [mkDIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨q', hq, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = q'.1 from (Fin.ext h1).symm]
    exact hq
  · intro h
    exact ⟨_, h, rfl⟩

def countMap {α : Type} [DecidableEq α] [Hashable α] (l : List α) : Std.HashMap α Nat :=
  l.reverse.foldl (fun (m : Std.HashMap α Nat) a => m.insert a (((m[a]?).getD 0) + 1)) ∅

theorem countMap_foldr {α : Type} [DecidableEq α] [Hashable α] (k : α) :
    ∀ (l : List α),
      ((l.foldr (fun a (m : Std.HashMap α Nat) => m.insert a (((m[a]?).getD 0) + 1)) ∅)[k]?).getD 0 =
        l.countP fun a => decide (a = k)
  | [] => by simp
  | a :: l => by
    simp only [List.foldr_cons, Std.HashMap.getElem?_insert, List.countP_cons]
    by_cases h : a = k
    · subst h
      have ih := countMap_foldr a l
      simp [ih]
    · have ih := countMap_foldr k l
      simp [h, ih]

theorem countMap_get {α : Type} [DecidableEq α] [Hashable α] (l : List α) (k : α) :
    ((countMap l)[k]?).getD 0 = l.countP fun a => decide (a = k) := by
  unfold countMap
  rw [← List.foldr_eq_foldl_reverse]
  exact countMap_foldr k l

def cardOKF {q : Nat} {α : Type} [DecidableEq α] [Hashable α] (f : Finset (Fin q) → α)
    (card : Finset (Fin q) → Option Nat) (tc : Std.HashMap α Nat)
    (τ : Finset (Fin q)) : Bool :=
  match card τ with
  | some k => decide (((tc[f τ]?).getD 0) ≤ k)
  | none => true

theorem cardOKF_eq {p q : Nat} (card : Finset (Fin q) → Option Nat)
    (Dn : List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))) (τ : Finset (Fin q)) :
    cardOKF SRI.Proc.toL card (countMap (Dn.map fun e => SRI.Proc.toL e.2)) τ =
      SRIQD.cardOK card Dn τ := by
  unfold cardOKF SRIQD.cardOK SRIQD.tcnt
  rw [countMap_get, List.countP_map, Function.comp_def]
  have h : (fun e : ContextCalculus.SRIQD.DNbr (Fin p) (Fin q) => decide (SRI.Proc.toL e.2 = SRI.Proc.toL τ)) =
      (fun e : ContextCalculus.SRIQD.DNbr (Fin p) (Fin q) => decide (e.2 = τ)) := by
    funext e
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact ⟨SRI.Proc.toL_inj, congrArg SRI.Proc.toL⟩
  cases card τ <;> simp [h]

def starGivenBF (ix : DIx n p q) (card : Finset (Fin q) → Option Nat)
    (t : Finset (Fin n)) (Dn : List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))) : Bool :=
  let lows := (SRI.Proc.toL t).flatMap fun a => getL ix.lowBy a.val
  let tc := countMap (Dn.map fun e => SRI.Proc.toL e.2)
  decide (Dn.length ≤ ix.bnd) &&
  Dn.all (fun e => lows.any fun c => decide (c.2.1 ∈ e.1 ∧ SRIQD.rngOK c.2.2.1 c.2.2.2 e.2)) &&
  (Dn.all (fun e => ix.dSub.all fun q' => !decide (q'.1 ∈ e.1) || decide (q'.2 ∈ e.1)) &&
   Dn.all (fun e => cardOKF SRI.Proc.toL card tc e.2) &&
   fAll t (fun a => (getL ix.allBy a.val).all fun c =>
     Dn.all fun e => !decide (c.1 ∈ e.1) || c.2.any fun l => decide (SRIQD.litOK l e.2)) &&
   fAll t (fun a => (getL ix.uppBy a.val).all fun c =>
     decide (SRIQD.dcnt Dn c.2.1 c.2.2.1 c.2.2.2 ≤ c.1))) &&
  lows.all (fun c => decide (c.1 ≤ SRIQD.dcnt Dn c.2.1 c.2.2.1 c.2.2.2))

theorem starGivenBF_eq (O : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (t : Finset (Fin n))
    (Dn : List (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))) :
    starGivenBF (mkDIx O) card t Dn = starGivenB O card t Dn := by
  apply Bool.eq_iff_iff.2
  unfold starGivenBF starGivenB SRIQD.Proc.dcandOK
  simp only [cardOKF_eq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true,
    List.mem_flatMap, SRI.Proc.mem_toL, fAll_iff, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, SRIQD.dok_iff, SRIQD.DDown, SRIQD.DLower, SRIQD.dcontrib,
    show (mkDIx O).bnd = SRIQD.dbnd O from rfl,
    show (mkDIx O).dSub = SRIQD.dSubL O from rfl,
    show (mkDIx O).lowBy = dLowBy O from rfl,
    show (mkDIx O).uppBy = dUppBy O from rfl,
    show (mkDIx O).allBy = dAllBy O from rfl,
    mem_dLowBy, mem_dUppBy, mem_dAllBy]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩
    have hd : SRIQD.DDown O card t Dn :=
      ⟨fun e he q' hq hu => (h3 e he q' hq).resolve_left (not_not.2 hu), h4,
       fun q' hq ht e he hu => (h5 q'.1 ht q'.2 hq e he).resolve_left (not_not.2 hu),
       fun q' hq ht => h6 q'.1 ht q'.2 hq⟩
    refine ⟨⟨h1, fun e he => ⟨SRIQD.dDown_sublist (List.singleton_sublist.2 he) hd, ?_⟩⟩, hd,
      fun q' hq ht => h7 q'.2 ⟨q'.1, ht, hq⟩⟩
    obtain ⟨c, ⟨a, ha, hc⟩, hok⟩ := h2 e he
    exact ⟨(a, c), hc, ha, hok⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4, h5, h6⟩, h7⟩
    refine ⟨⟨⟨h1, fun e he => ?_⟩, ⟨⟨fun e he q' hq => ?_, h4⟩, fun a ha c hc e he => ?_⟩,
      fun a ha c hc => h6 (a, c) hc ha⟩, ?_⟩
    · obtain ⟨q', hq, ht, hok⟩ := (h2 e he).2
      exact ⟨q'.2, ⟨q'.1, ht, hq⟩, hok⟩
    · by_cases hu : q'.1 ∈ e.1
      · exact Or.inr (h3 e he q' hq hu)
      · exact Or.inl hu
    · by_cases hu : c.1 ∈ e.1
      · exact Or.inr (h5 (a, c) hc ha e he hu)
      · exact Or.inl hu
    · rintro c ⟨a, ha, hc⟩
      exact h7 (a, c) hc ha

def okOfF {p q : Nat} (ix : DIx n p q) (Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (h : HintS n m)
    (stars : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))))
    (b : Fin h.k) : Bool :=
  match (stars[b.val]?).getD none with
  | some l => if l.all Option.isSome then starGivenBF ix card (h.tyF b) (l.filterMap id) else false
  | none => SRIQD.Proc.dataSatB Db card (h.tyF b)

theorem okOfF_eq {p q : Nat} (Db : SRIQD.Ontology (Fin n) (Fin m) (Fin p) (Fin q))
    (card : Finset (Fin q) → Option Nat) (h : HintS n m)
    (stars : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q))))))
    (b : Fin h.k) :
    okOfF (mkDIx Db) Db card h stars b = okOf Db card h stars b := by
  unfold okOfF okOf
  split
  · split_ifs
    · exact starGivenBF_eq Db card (h.tyF b) _
    · rfl
  · rfl

/-- The value types of the given data stars. -/
def starTaus {p q : Nat} (stars : Array (Option (List (Option (ContextCalculus.SRIQD.DNbr (Fin p) (Fin q)))))) :
    List (Finset (Fin q)) :=
  (stars.toList.flatMap fun o => (o.getD []).filterMap fun e => e.map Prod.snd).eraseDups

/-- **`hintPartsS` with the named part and the given data stars**: a hint
that names a part is checked on that part only, otherwise on every part;
a core element with a given data star is checked on that star (no search). -/
def hintPartsP (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let Dd := dataOnly Db
  let A := SRIQD.objPart Db
  let N := dnoms D
  let ix := mkSIx A
  let noKids := h.kids.isEmpty
  let sc := cells.filter sp
  let stars := starsOf (p := p) (q := q) h
  let taus := starTaus stars
  let okAll := fun (card0 : Finset (Fin q) → Option Nat) =>
    let tab := memoTab card0 taus
    let card := lookCard card0 tab
    (List.finRange h.k).all (fun b => okOf Dd card h stars b) &&
      (noKids || h.recs.all (fun e => SRIQD.Proc.dataSatB Dd card e.ty))
  (coreB h ix N && (noKids || certB h ix N)) &&
  if h.partNamed then
    let x := namedPart sc (ContextCalculus.SRIQD.allG s).length h.part
    validPartB size s sc x && okAll (partCardT (partTab cells size sp E (toPart s x)))
  else (partsOf size s sc).any fun x => okAll (partCardT (partTab cells size sp E (toPart s x)))

/-- `hintPartsP` with indexed data clauses (`mkDIx`) and direct hash-table oracle (`partCardTF`). -/
def hintPartsPF (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let Dd := dataOnly Db
  let ixD := mkDIx Dd
  let A := SRIQD.objPart Db
  let N := dnoms D
  let ix := mkSIx A
  let noKids := h.kids.isEmpty
  let sc := cells.filter sp
  let stars := starsOf (p := p) (q := q) h
  let okAll := fun (card : Finset (Fin q) → Option Nat) =>
    (List.finRange h.k).all (fun b => okOfF ixD Dd card h stars b) &&
      (noKids || h.recs.all (fun e => SRIQD.Proc.dataSatB Dd card e.ty))
  (coreB h ix N && (noKids || certB h ix N)) &&
  if h.partNamed then
    let x := namedPart sc (ContextCalculus.SRIQD.allG s).length h.part
    validPartB size s sc x && okAll (partCardTS (partTab cells size sp E (toPart s x))).f
  else (partsOf size s sc).any fun x => okAll (partCardTS (partTab cells size sp E (toPart s x))).f

@[simp] theorem lookCard_memoTab {q : Nat} (c : Finset (Fin q) → Option Nat) (L : List (Finset (Fin q))) :
    lookCard c (memoTab c L) = c :=
  memoCard_eq c L

@[csimp] theorem hintPartsP_eq_F : @hintPartsP = @hintPartsPF := by
  funext n m K _ q s p O cells size sp E h
  unfold hintPartsP hintPartsPF
  dsimp only
  simp only [lookCard_memoTab, partCardTS_f, okOfF_eq]

/-- `hintPartsPF` using `partTabV` and `toPartHS`. -/
def hintPartsPV [Hashable K] (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (vtcF : K → (Fin s → Bool) → Finset (Fin q))
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let Dd := dataOnly Db
  let ixD := mkDIx Dd
  let A := SRIQD.objPart Db
  let N := dnoms D
  let ix := mkSIx A
  let noKids := h.kids.isEmpty
  let sc := cells.filter sp
  let stars := starsOf (p := p) (q := q) h
  let okAll := fun (card : Finset (Fin q) → Option Nat) =>
    (List.finRange h.k).all (fun b => okOfF ixD Dd card h stars b) &&
      (noKids || h.recs.all (fun e => SRIQD.Proc.dataSatB Dd card e.ty))
  (coreB h ix N && (noKids || certB h ix N)) &&
  if h.partNamed then
    let x := namedPart sc (ContextCalculus.SRIQD.allG s).length h.part
    validPartB size s sc x && okAll (partCardTS (partTabV cells size sp vtcF (toPartHS s x).f)).f
  else (partsOf size s sc).any fun x => okAll (partCardTS (partTabV cells size sp vtcF (toPartHS s x).f)).f

theorem hintPartsPV_eq [Hashable K] (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (vtcF : K → (Fin s → Bool) → Finset (Fin q)) (hvtc : ∀ c g, vtcF c g = SRIQD.vtc E c g)
    (h : HintS (n + Proc.encKD O) m) :
    hintPartsPV O cells size sp vtcF h = hintPartsP O cells size sp E h := by
  rw [hintPartsP_eq_F]
  unfold hintPartsPV hintPartsPF
  simp only [partTabV_eq cells size sp E vtcF hvtc, toPartHS_f]

theorem hintPartsP_imp (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) (hh : hintPartsP O cells size sp E h = true) :
    hintPartsN O cells size sp E h.toN = true := by
  rw [hintPartsN_eq_F]
  unfold hintPartsP at hh
  unfold hintPartsNF
  have hmc : ∀ (c : Finset (Fin q) → Option Nat) (L : List (Finset (Fin q))),
      lookCard c (memoTab c L) = c := memoCard_eq
  simp only [hmc, partCardT_eq] at hh
  dsimp only at hh ⊢
  have hk : ((List.finRange h.toN.k).all fun b => (h.toN.kids b).isEmpty) = h.kids.isEmpty :=
    noKids_eq h
  rw [← coreB_eq, ← certB_eq, hk]
  have hrec : ∀ ok : Finset (Fin (n + Proc.encKD O)) → Bool,
      (h.toN.recs.all fun e => ok e.1.1) = h.recs.all fun e => ok e.ty := fun ok => by
    simp [HintS.toN, RecS.toN, List.all_map, Function.comp_def]
  simp only [hrec]
  rw [Bool.and_eq_true] at hh
  obtain ⟨h1, h2⟩ := hh
  -- the all-elements test of a part follows from the given stars
  have hall : ∀ card, ((List.finRange h.k).all (fun b => okOf (dataOnly (dbase (Proc.encTransDN O))) card h
        (starsOf (p := p) (q := q) h) b) &&
      (h.kids.isEmpty || h.recs.all (fun e => SRIQD.Proc.dataSatB (dataOnly (dbase (Proc.encTransDN O))) card e.ty))) = true →
      ((List.finRange h.toN.k).all (fun b => SRIQD.Proc.dataSatB (dbase (Proc.encTransDN O)) card (h.toN.ty b)) &&
        (h.kids.isEmpty || h.recs.all (fun e => SRIQD.Proc.dataSatB (dbase (Proc.encTransDN O)) card e.ty))) = true := by
    intro card hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc ⊢
    refine ⟨fun b hb => ?_, ?_⟩
    · have := okOf_imp (hc.1 b hb)
      rwa [dataSatB_dataOnly] at this
    · rw [← dataSatB_dataOnly]; exact hc.2
  rw [Bool.and_eq_true]
  refine ⟨h1, ?_⟩
  rw [List.any_eq_true]
  split_ifs at h2
  · rw [Bool.and_eq_true] at h2
    exact ⟨_, mem_of_validPartB h2.1, hall _ h2.2⟩
  · obtain ⟨x, hx, hx2⟩ := List.any_eq_true.1 h2
    exact ⟨x, hx, hall _ hx2⟩

/-- `hintPartsP` with loops at nominal elements. -/
def hintPartsNLP (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  loopOKS h (dnoms (Proc.encTransDN O)) && hintPartsP O cells size sp E h

theorem hintPartsNLP_imp (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) (hh : hintPartsNLP O cells size sp E h = true) :
    hintPartsNL O cells size sp E h.toN = true := by
  unfold hintPartsNLP at hh
  rw [Bool.and_eq_true] at hh
  rw [hintPartsNL_eq_F]
  unfold hintPartsNLF
  rw [← loopOKS_eq, hh.1, ← hintPartsN_eq_F, hintPartsP_imp O cells size sp E h hh.2]
  rfl

/-- `hintPartsP` (or `hintPartsNLP`) over a list of hints. -/
def hintPartsPB (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (loops : Bool) (hs : List (Option (HintS (n + Proc.encKD O) m))) : List Bool :=
  hs.map fun h => h.any fun h =>
    if loops then hintPartsNLP O cells size sp E h else hintPartsP O cells size sp E h

theorem hintPartsPB_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hs : List (Option (HintS (n + Proc.encKD O) m))) :
    hintPartsPB O cells size sp E false hs = hs.map (fun h => h.any (hintPartsP O cells size sp E)) ∧
    hintPartsPB O cells size sp E true hs = hs.map (fun h => h.any (hintPartsNLP O cells size sp E)) :=
  ⟨rfl, rfl⟩

def hintPartsNLPV [Hashable K] (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (vtcF : K → (Fin s → Bool) → Finset (Fin q))
    (h : HintS (n + Proc.encKD O) m) : Bool :=
  loopOKS h (dnoms (Proc.encTransDN O)) && hintPartsPV O cells size sp vtcF h

theorem hintPartsNLPV_eq [Hashable K] (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (vtcF : K → (Fin s → Bool) → Finset (Fin q)) (hvtc : ∀ c g, vtcF c g = SRIQD.vtc E c g)
    (h : HintS (n + Proc.encKD O) m) :
    hintPartsNLPV O cells size sp vtcF h = hintPartsNLP O cells size sp E h := by
  unfold hintPartsNLPV hintPartsNLP
  rw [hintPartsPV_eq O cells size sp E vtcF hvtc h]

def hintPartsPBV [Hashable K] (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (vtcF : K → (Fin s → Bool) → Finset (Fin q))
    (loops : Bool) (hs : List (Option (HintS (n + Proc.encKD O) m))) : List Bool :=
  hs.map fun h => h.any fun h =>
    if loops then hintPartsNLPV O cells size sp vtcF h else hintPartsPV O cells size sp vtcF h

theorem hintPartsPBV_eq [Hashable K] (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (vtcF : K → (Fin s → Bool) → Finset (Fin q)) (hvtc : ∀ c g, vtcF c g = SRIQD.vtc E c g)
    (loops : Bool) (hs : List (Option (HintS (n + Proc.encKD O) m))) :
    hintPartsPBV O cells size sp vtcF loops hs = hintPartsPB O cells size sp E loops hs := by
  unfold hintPartsPBV hintPartsPB
  simp only [hintPartsNLPV_eq O cells size sp E vtcF hvtc,
    hintPartsPV_eq O cells size sp E vtcF hvtc]

/-- `hintPartsS` over a list of hints, the encodings and the index computed once. -/
def hintPartsSB (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (loops : Bool) (hs : List (Option (HintS (n + Proc.encKD O) m))) : List Bool :=
  let D := Proc.encTransDN O
  let Db := dbase D
  let A := SRIQD.objPart Db
  let N := dnoms D
  let ix := mkSIx A
  let xs := (partsOf size s (cells.filter sp)).map fun x => toPart s x
  hs.map fun h => h.any fun h =>
    let noKids := h.kids.isEmpty
    (!loops || loopOKS h N) &&
    ((coreB h ix N && (noKids || certB h ix N)) &&
    xs.any fun x =>
      let ok := SRIQD.Proc.dataSatB (dataOnly Db) (partCard cells size sp E x)
      (List.finRange h.k).all (fun b => ok (h.tyF b)) && (noKids || h.recs.all (fun e => ok e.ty)))

theorem hintPartsSB_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (hs : List (Option (HintS (n + Proc.encKD O) m))) :
    hintPartsSB O cells size sp E false hs = hs.map (fun h => h.any (hintPartsS O cells size sp E)) ∧
    hintPartsSB O cells size sp E true hs = hs.map (fun h => h.any (hintPartsNLS O cells size sp E)) := by
  constructor
  · simp only [hintPartsSB, hintPartsS, hintPartsNLS, List.any_map, Function.comp_def,
      Bool.not_false, Bool.true_or, Bool.true_and]
    rfl
  · simp only [hintPartsSB, hintPartsS, hintPartsNLS, List.any_map, Function.comp_def,
      Bool.not_true, Bool.false_or]
    rfl

end Parts

end ContextCalculus.SRIQN.HF

#print axioms ContextCalculus.SRIQN.HF.starF_iff
#print axioms ContextCalculus.SRIQN.HF.checkRedS_eq
#print axioms ContextCalculus.SRIQN.HF.hintPartsS_eq
#print axioms ContextCalculus.SRIQN.HF.hintPartsNLS_eq
#print axioms ContextCalculus.SRIQN.HF.hintPartsSB_eq
#print axioms ContextCalculus.SRIQN.HF.hintPartsP_imp
#print axioms ContextCalculus.SRIQN.HF.hintPartsNLP_imp
#print axioms ContextCalculus.SRIQN.HF.hintPartsPB_eq
#print axioms ContextCalculus.SRIQN.HF.lookSplit_eq
#print axioms ContextCalculus.SRIQN.HF.toN_eq_F
#print axioms ContextCalculus.SRIQN.HF.coreB_eq_F
#print axioms ContextCalculus.SRIQN.HF.namedPart_eq_F
#print axioms ContextCalculus.SRIQN.HF.partCardTS_f
#print axioms ContextCalculus.SRIQN.HF.hintPartsP_eq_F
