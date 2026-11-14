import ContextCalculus.SRIQ.FastCheckA

/-!
# Certificate check for the fast SHIQ procedure: the array check is sound (stage C1d)

`closedFastB_sound`: when the array check accepts an array candidate set,
the finset candidate set it denotes satisfies the closure conditions
`ClosedP` of `FastDefs.lean`. Each condition of the array check computes
the same lists as the finset definition, up to the view of arrays as
finsets (`lowAtA_eq`, `backLists_view`, `cset_view`, `pot_view`,
`ddef_view`), or a sound part of it (pool lookups, `brCovA`).
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-! ## Well-formedness -/

/-- Every array of the candidate set is sorted; names of node types and
specs are below `n`, role codes of specs below `2 m`. -/
structure WF (n m : Nat) (C : CandA) : Prop where
  ty : ∀ i, SortedA (ndA C i).ty
  tyB : ∀ i, ∀ x ∈ (ndA C i).ty, x < n
  ent : ∀ i, ∀ e ∈ (ndA C i).pool,
    SortedA e.lab ∧ (∀ x ∈ e.lab, x < 2 * m) ∧ SortedA e.fill ∧ ∀ x ∈ e.fill, x < n
  seed : ∀ k, SortedA (keyA C k).seed
  lab : ∀ k, SortedA (keyA C k).lab
  pi : ∀ k, SortedA (keyA C k).pi
  bk : ∀ j, SortedA (bkA C j)
  bkB : ∀ j, ∀ x ∈ bkA C j, x < n
  uni : ∀ k, SortedA (uniA C k)

theorem all_getD {α : Type} {a : Array α} {p : α → Bool} (h : a.all p = true) {d : α}
    (hd : p d = true) (i : Nat) : p (a[i]?.getD d) = true := by
  by_cases hi : i < a.size
  · rw [Array.getElem?_eq_getElem hi, Option.getD_some]
    exact Array.all_eq_true.1 h i hi
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none]
    exact hd

theorem all_mem {a : Array Nat} {p : Nat → Bool} (h : a.all p = true) {x : Nat} (hx : x ∈ a) :
    p x = true := by
  rw [← Array.all_toList, List.all_eq_true] at h
  exact h x (Array.mem_def.1 hx)

theorem wfB_sound {C : CandA} (h : wfB n m C = true) : WF n m C := by
  simp only [wfB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hn, hk⟩, hb⟩, hu⟩ := h
  have hN := fun i => all_getD hn (d := default) (by simp [wfNode, default_nodeA, sortedB, ascL]) i
  have hK := fun k => all_getD hk (d := default) (by simp [wfKey, default_keyA, sortedB, ascL]) k
  have hB := fun j => all_getD hb (d := #[]) (by simp [sortedB, ascL]) j
  simp only [Bool.and_eq_true] at hB
  have hU := fun k => all_getD hu (d := #[]) (by simp [sortedB, ascL]) k
  simp only [wfNode, wfKey, Bool.and_eq_true, List.all_eq_true] at hN hK
  refine ⟨fun i => sortedB_sound (hN i).1.1, fun i x hx => ?_, fun i e he => ?_,
    fun k => sortedB_sound (hK k).1.1, fun k => sortedB_sound (hK k).1.2,
    fun k => sortedB_sound (hK k).2, fun j => sortedB_sound (hB j).1,
    fun j x hx => by simpa using all_mem (hB j).2 hx, fun k => sortedB_sound (hU k)⟩
  · simpa using all_mem (hN i).1.2 hx
  · obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := (hN i).2 e he
    exact ⟨sortedB_sound h1, fun x hx => by simpa using all_mem h2 hx, sortedB_sound h3,
      fun x hx => by simpa using all_mem h4 hx⟩

/-! ## Basic computations -/

section Basic

variable (ix : Ix n m)

theorem lowAtA_eq {T : Array Nat} (hT : SortedA T) : lowAtA ix T = lowAt ix (absTy n T) := by
  simp only [lowAtA, lowAtF, lowAt, sort_absTy hT]

theorem uppAtA_eq {T : Array Nat} (hT : SortedA T) : uppAtA ix T = uppAt ix (absTy n T) := by
  simp only [uppAtA, uppAtF, uppAt, sort_absTy hT]

theorem pcBA_eq {κ : KeyA} (hl : SortedA κ.lab) (hp : SortedA κ.pi) (R : RoleT (Fin m)) (b : Fin n) :
    pcBA κ R b = pcB (viewKey n m κ) R b := by
  simp only [pcBA, pcB, viewKey, Bool.and_eq_true, bsA_iff hl, bsA_iff hp, mem_absLab, mem_absTy]

theorem skipQA_iff {κ : KeyA} (hl : SortedA κ.lab) (hp : SortedA κ.pi)
    (q : Fin n × Nat × RoleT (Fin m) × Fin n) :
    skipQA κ q = true ↔ skipQ (viewKey n m κ) q := by
  simp only [skipQA, skipQ, Bool.and_eq_true, beq_iff_eq, pcBA_eq hl hp]

theorem mem_fwdL {T L : Array Nat} (hL : SortedA L) (y : Fin n) :
    y.val ∈ fwdL (abOf ix (finL n T.toList)) L ↔ y ∈ fwdI ix (absTy n T) (absLab m L) := by
  simp only [fwdL, abOf, fwdI, List.mem_flatMap, List.mem_map, List.mem_filter, Finset.mem_biUnion,
    List.mem_toFinset, bsA_iff hL, mem_absLab, absTy, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨⟨a, ha, hp⟩, hS⟩, he⟩
    exact ⟨a, ha, p, ⟨hp, hS⟩, Fin.ext he⟩
  · rintro ⟨a, ha, p, ⟨hp, hS⟩, rfl⟩
    exact ⟨p, ⟨⟨a, ha, hp⟩, hS⟩, rfl⟩

theorem absTy_canon_fwd {F T L : Array Nat} (hL : SortedA L) :
    absTy n (canon (F.toList ++ fwdL (abOf ix (finL n T.toList)) L)) =
      absTy n F ∪ fwdI ix (absTy n T) (absLab m L) := by
  refine absTy_canon fun y => ?_
  rw [Finset.mem_union, mem_absTy, List.mem_append, ← mem_fwdL ix hL, Array.mem_def]

theorem absTy_canon_fwd' {T L : Array Nat} (hL : SortedA L) :
    absTy n (canon (fwdL (abOf ix (finL n T.toList)) L)) = fwdI ix (absTy n T) (absLab m L) := by
  refine absTy_canon fun y => ?_
  rw [← mem_fwdL ix hL]

theorem closedIA_sound {T : Array Nat} (hT : SortedA T) (h : closedIA ix T (finL n T.toList) = true) :
    closedI ix (absTy n T) := by
  simp only [closedIA, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', bsA_iff hT] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun g hg => ?_, fun a ha g hg hb => ?_⟩
  · obtain ⟨x, hx, hxT⟩ := h1 g hg
    exact ⟨x, hx, mem_absTy.2 hxT⟩
  · have ha' : a ∈ finL n T.toList := by rw [mem_finL]; exact Array.mem_def.1 (mem_absTy.1 ha)
    rcases h2 a ha' g hg with h | ⟨x, hx, hxT⟩
    · exfalso
      rw [Bool.eq_false_iff] at h
      apply h
      simp only [List.all_eq_true, bsA_iff hT]
      exact fun b hb' => mem_absTy.1 (hb b hb')
    · exact ⟨x, hx, mem_absTy.2 hxT⟩

theorem upClosedA_sound {L : Array Nat} (hL : SortedA L) (h : upClosedA ix L = true) :
    upClosedB ix (absLab m L) := by
  intro R hR S hS
  have := all_mem h (mem_absLab.1 hR)
  simp only [List.all_eq_true, bsA_iff hL] at this
  exact mem_absLab.2 (this S hS)

end Basic

/-! ## Nodes and entries -/

section Nodes

variable {O : Ontology (Fin n) (Fin m)} {C : CandA}

theorem view_nd_ty (i : Nat) : (nd (C.view n m) i).ty = absTy n (ndA C i).ty := by
  rw [nd_view]; rfl

theorem view_nd_ctx (i : Nat) : (nd (C.view n m) i).ctx = (ndA C i).ctx := by
  rw [nd_view]; rfl

theorem view_nd_pool (i : Nat) : (nd (C.view n m) i).pool = (ndA C i).pool.map (viewEntry n m) := by
  rw [nd_view]; rfl

theorem view_key_ctx (i : Nat) :
    keyOf (C.view n m) (nd (C.view n m) i).ctx = viewKey n m (keyA C (ndA C i).ctx) := by
  rw [view_nd_ctx, keyOf_view]

theorem nodeOKA_sound (hW : WF n m C) {i : Nat}
    (h : nodeOKA (mkIx O) C i (finL n (ndA C i).ty.toList) = true) :
    nodeOK (mkIx O) (C.view n m) i := by
  simp only [nodeOKA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨by simpa using h1, by rw [view_nd_ctx]; simpa using h2, ?_, ?_⟩
  · rw [view_nd_ty]; exact closedIA_sound _ (hW.ty i) h3
  · intro y hy
    rw [view_key_ctx] at hy
    rw [view_nd_ty, mem_absTy]
    have := all_mem h4 (mem_absTy.1 hy)
    exact (bsA_iff (hW.ty i)).1 this

theorem childKeyA_view {T : Array Nat} {e : EntryA} (hl : SortedA e.lab) :
    viewKey n m (childKeyA (mkIxF O (mkIx O)) T (abOf (mkIx O) (finL n T.toList)) e) =
      childKey (mkIx O) (absTy n T) (viewEntry n m e).spec := by
  simp only [childKeyA, childKey, viewKey, viewEntry, Key.mk.injEq]
  refine ⟨absTy_canon_fwd _ hl, absLab_flipA _, ?_⟩
  ext y
  rw [mem_absTy, Array.mem_filter, Finset.mem_inter, mem_absTy, flipA,
    relHitA_iff (sorted_canon _), ← flipA, absLab_flipA]

theorem entryOKA_sound (hW : WF n m C) {i : Nat} {e : EntryA} (he : e ∈ (ndA C i).pool)
    (h : entryOKA (mkIx O) (mkIxF O (mkIx O)) C (ndA C i).ty
      (abOf (mkIx O) (finL n (ndA C i).ty.toList)) e = true) :
    entryOK (mkIx O) (C.view n m) (nd (C.view n m) i).ty (viewEntry n m e) := by
  simp only [entryOKA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hl := (hW.ent i e he).1
  refine ⟨by simpa [viewEntry] using h1, ?_, upClosedA_sound _ hl h3⟩
  rw [view_nd_ty, keyOf_view]
  simp only [viewEntry] at *
  rw [h2]
  exact childKeyA_view hl

theorem poolSet_sound {i : Nat} {l f : Array Nat}
    (h : (poolSet (ndA C i)).contains (l, f) = true) :
    inPool (C.view n m) i ⟨absLab m l, absTy n f⟩ := by
  rw [poolSet, Std.HashSet.contains_ofList, List.contains_iff_mem, List.mem_map] at h
  obtain ⟨e, he, hef⟩ := h
  simp only [Prod.mk.injEq] at hef
  refine ⟨viewEntry n m e, ?_, ?_⟩
  · rw [view_nd_pool]; exact List.mem_map.2 ⟨e, he, rfl⟩
  · simp [viewEntry, hef.1, hef.2]

theorem r3A_sound (hW : WF n m C) {i : Nat}
    (h : r3A (mkIxF O (mkIx O)) (keyA C (ndA C i).ctx) (lowAtA (mkIx O) (ndA C i).ty)
      (poolSet (ndA C i)) = true) :
    ∀ q ∈ lowAt (mkIx O) (nd (C.view n m) i).ty, 1 ≤ q.2.1 →
      ¬ skipQ (keyOf (C.view n m) (nd (C.view n m) i).ctx) q →
      inPool (C.view n m) i (dflt (mkIx O) q) := by
  intro q hq hk hs
  rw [view_nd_ty, ← lowAtA_eq _ (hW.ty i)] at hq
  rw [view_key_ctx] at hs
  simp only [r3A, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h q hq with (h | h) | h
  · exact absurd hk h
  · exact absurd ((skipQA_iff (hW.lab _) (hW.pi _) q).1 h) hs
  · have := poolSet_sound (n := n) (m := m) h
    rw [absLab_upSA, absTy_single] at this
    exact this

end Nodes

/-! ## Branches -/

section Branch

variable {ix : Ix n m}

theorem brAuxA_cover : ∀ (f : Nat) (cur : Ty n) (q : List Nat) (H : Std.HashSet Nat),
    (∀ y : Fin n, y ∈ cur ↔ H.contains y.val = true) →
    ∀ b ∈ brAux ix f cur q, ∃ H' ∈ brAuxA ix f H q, ∀ y : Fin n, y ∈ b ↔ H'.contains y.val = true := by
  intro f cur q
  induction f, cur, q using brAux.induct (ix := ix) with
  | case1 cur q =>
    intro H hH b hb
    simp only [brAux, List.mem_singleton] at hb
    subst hb
    exact ⟨H, by simp [brAuxA], hH⟩
  | case2 f cur =>
    intro H hH b hb
    simp only [brAux, List.mem_singleton] at hb
    subst hb
    exact ⟨H, by simp [brAuxA], hH⟩
  | case3 f cur i rest hg ih =>
    intro H hH b hb
    rw [brAux, hg] at hb
    obtain ⟨H', hH', h'⟩ := ih H hH b hb
    refine ⟨H', ?_, h'⟩
    rw [brAuxA, hg]
    exact hH'
  | case4 f cur i rest g hg hfire ih =>
    intro H hH b hb
    simp only [brAux, hg] at hb
    rw [if_pos hfire] at hb
    obtain ⟨h, hh, hb⟩ := List.mem_flatMap.1 hb
    have hrel : ∀ y : Fin n, y ∈ insert h cur ↔ (H.insert h.val).contains y.val = true := by
      intro y
      rw [Finset.mem_insert, Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, hH,
        Fin.val_eq_val, eq_comm]
    obtain ⟨H', hH', h'⟩ := ih h (H.insert h.val) hrel b hb
    refine ⟨H', ?_, h'⟩
    rw [brAuxA]
    simp only [hg]
    have hc : ((g.1.all fun b => H.contains b.val) && (g.2.all fun h => !H.contains h.val)) = true := by
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
      refine ⟨fun b hb => (hH b).1 (hfire.1 b hb), fun h hh => ?_⟩
      rw [Bool.eq_false_iff]
      exact fun hc => hfire.2 h hh ((hH h).2 hc)
    rw [if_pos hc]
    have hmem : H' ∈ g.2.flatMap fun h => brAuxA ix f (H.insert h.val) (getL ix.gciBy h.val ++ rest) :=
      List.mem_flatMap.2 ⟨h, hh, hH'⟩
    revert hmem
    generalize g.2 = l
    intro hmem
    match l, hmem with
    | [], hmem => simp at hmem
    | [h0], hmem => simpa using hmem
    | _ :: _ :: _, hmem => exact hmem
  | case5 f cur i rest g hg hfire ih =>
    intro H hH b hb
    simp only [brAux, hg] at hb
    rw [if_neg hfire] at hb
    obtain ⟨H', hH', h'⟩ := ih H hH b hb
    refine ⟨H', ?_, h'⟩
    rw [brAuxA]
    simp only [hg]
    have hc : ((g.1.all fun b => H.contains b.val) && (g.2.all fun h => !H.contains h.val)) = false := by
      rw [Bool.eq_false_iff]
      intro hc
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hc
      refine hfire ⟨fun b hb => (hH b).2 (hc.1 b hb), fun h hh hin => ?_⟩
      have := hc.2 h hh
      rw [(hH h).1 hin] at this
      exact Bool.noConfusion this
    rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
    exact hH'

theorem brCovA_sound {C : CandA} {k : Nat} {s : Array Nat} (hs : SortedA s)
    (h : brCovA ix C k s = true) : BranchCov ix (C.view n m) k (absTy n s) := by
  intro b hb
  simp only [br, sort_absTy hs] at hb
  obtain ⟨H, hH, hrel⟩ := brAuxA_cover _ _ _ (Std.HashSet.ofList s.toList) (fun y => by
    rw [Std.HashSet.contains_ofList, List.contains_iff_mem, mem_absTy, Array.mem_def]) b hb
  simp only [brCovA, List.all_eq_true, List.any_eq_true, List.mem_filter] at h
  obtain ⟨j, ⟨hj, hsj⟩, hjH⟩ := h H hH
  refine ⟨j, by rw [memb_view]; exact hj, ?_, ?_⟩
  · intro y hy
    rw [view_nd_ty, mem_absTy]
    exact bsA_sound (all_mem hsj (mem_absTy.1 hy))
  · intro y hy
    rw [view_nd_ty, mem_absTy] at hy
    exact (hrel y).2 (all_mem hjH hy)

end Branch

end ContextCalculus.SRIQ.Fast
