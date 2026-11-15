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

/-- Universals across the edge `e` from a centre of type `t` with mask `M`. -/
def edgeB (ix : SIx n m) (M : Array Bool) (t : Finset (Fin n)) (e : QNbr n m) : Bool :=
  fAll t (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1 ∈ e.1) || decide (p.2 ∈ e.2)) &&
  fAll e.2 (fun a => (getL ix.allBy a.val).all fun p => !decide (p.1.flip ∈ e.1) || memM M p.2)

/-- The gcis at a type with mask `M`. -/
def closedB (ix : SIx n m) (M : Array Bool) (t : Finset (Fin n)) : Bool :=
  ix.gTop.all (fun h => h.any (memM M)) &&
  fAll t (fun a => (getL ix.gBy a.val).all fun g => !(g.1.all (memM M)) || g.2.any (memM M))

/-- **The star condition through the index.** -/
def starF (ix : SIx n m) (t : Finset (Fin n)) (N : List (QNbr n m)) : Bool :=
  let M := mask t
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
    edgeB (mkSIx O) (mask t) t e = true ↔ EdgeOK O t e := by
  unfold edgeB EdgeOK
  simp only [Bool.and_eq_true, fAll_iff, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq, memM_mask_iff]
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

theorem closedB_iff (t : Finset (Fin n)) : closedB (mkSIx O) (mask t) t = true ↔ Closed O t := by
  unfold closedB
  rw [SRIQ.closed_iff]
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, fAll_iff, Bool.or_eq_true,
    Bool.not_eq_true', memM_mask_iff]
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
        simp only [memM_mask_iff] at hxn
        exact hxn (hb x hx)
      · exact h
  · intro h
    refine ⟨fun hd hh => h [] hd (mem_gTop.1 hh) (by simp), fun a _ g hg => ?_⟩
    by_cases hb : g.1.all (memM (mask t)) = true
    · right
      rw [List.all_eq_true] at hb
      exact h g.1 g.2 (mem_gBy.1 hg).2 fun x hx => (memM_mask_iff t x).1 (hb x hx)
    · left
      simpa using hb

/-- **The indexed star is the star.** -/
theorem starF_iff (t : Finset (Fin n)) (N : List (QNbr n m)) :
    starF (mkSIx O) t N = true ↔ StarOK O t N := by
  rw [SRIQ.Proc.starOK_iff]
  unfold starF
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
def nomOKS (N : List (Fin n)) : Bool :=
  let nm := maskL n N
  let own := buildIdx n some ((List.finRange h.k).flatMap fun b =>
    ((h.tyF b).sort (· ≤ ·)).filterMap fun a => if memM nm a then some (a.val, b) else none)
  N.all fun a => match getL own a.val with
    | [] => false
    | b :: rest => rest.all (· = b)

theorem nomOKS_iff (N : List (Fin n)) : nomOKS h N = true ↔ NomOK N h.toN.ty := by
  unfold nomOKS NomOK
  simp only [List.all_eq_true]
  have hown : ∀ a ∈ N, ∀ b, b ∈ getL (buildIdx n some ((List.finRange h.k).flatMap fun b =>
      ((h.tyF b).sort (· ≤ ·)).filterMap fun a =>
        if memM (maskL n N) a then some (a.val, b) else none)) a.val ↔ a ∈ h.toN.ty b := by
    intro a ha b
    rw [mem_buildIdx a.isLt]
    simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_filterMap,
      Option.some.injEq, Finset.mem_sort, memM_maskL]
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

/-- The core conditions and the stars of the core elements. -/
def coreB (ix : SIx n m) (N : List (Fin n)) : Bool :=
  let A := h.adj
  let kb := h.kidIdx
  decide (0 < h.k) && nomOKS h N &&
    (List.finRange h.k).all fun b => starF ix (h.tyF b) (h.starL A b ++ getL kb b.val)

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
    let ok := SRIQD.Proc.dataSatB Db (partCard cells size sp E (toPart s x))
    (List.finRange h.k).all (fun b => ok (h.tyF b)) && (noKids || h.recs.all (fun e => ok e.ty))

theorem hintPartsS_eq (O : DOntology (Fin n) (Fin m) (Fin p) (Fin q)) (cells : List K)
    (size : K → Option Nat) (sp : K → Bool) (E : Fin q → K → (Fin s → Bool) → Bool)
    (h : HintS (n + Proc.encKD O) m) :
    hintPartsS O cells size sp E h = hintPartsN O cells size sp E h.toN := by
  rw [hintPartsN_eq_F]
  unfold hintPartsS hintPartsNF
  dsimp only
  simp only [coreB_eq, certB_eq, ← noKids_eq h]
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
      let ok := SRIQD.Proc.dataSatB Db (partCard cells size sp E x)
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
