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

/-! ## The back rule -/

section Back

variable {O : Ontology (Fin n) (Fin m)} {C : CandA}

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem needsL_view (hW : WF n m C) (i : Nat) :
    needsL (mkIx O) (C.view n m) i =
      needsLA (keyA C (ndA C i).ctx) (lowAtA (mkIx O) (ndA C i).ty) := by
  simp only [needsL, needsLA, view_nd_ty, view_key_ctx, ← lowAtA_eq _ (hW.ty i)]
  refine List.filter_congr fun q _ => ?_
  rw [pcBA_eq (hW.lab _) (hW.pi _)]

theorem candsQ_view (hW : WF n m C) (i : Nat) (q : Fin n × Nat × RoleT (Fin m) × Fin n) :
    candsQ (C.view n m) i q =
      (candsQA C (ndA C i) q).map fun p => (viewEntry n m p.1, p.2) := by
  simp only [candsQ, candsQA, view_nd_pool, List.flatMap_map, List.map_flatMap]
  refine flatMap_congr' fun e he => ?_
  have hl := (hW.ent i e he).1
  simp only [viewEntry, mem_absLab]
  by_cases hR : rc q.2.2.1 ∈ e.lab
  · rw [if_pos hR, if_pos ((bsA_iff hl).2 hR), memb_view, List.map_map]
    rw [List.filter_congr (q := fun j => bsA (ndA C j).ty q.2.2.2.val) fun j _ => by
      rw [view_nd_ty, Bool.eq_iff_iff, decide_eq_true_iff, mem_absTy, bsA_iff (hW.ty j)]]
    rfl
  · rw [if_neg hR, if_neg (by rw [bsA_iff hl]; exact hR)]
    rfl

theorem backLists_view (hW : WF n m C) (i : Nat) :
    backLists (mkIx O) (C.view n m) i =
      (backListsA C (ndA C i) (keyA C (ndA C i).ctx) (lowAtA (mkIx O) (ndA C i).ty)).map
        (List.map (absTy n)) := by
  simp only [backLists, backListsA, needsL_view hW, candsQ_view hW, List.map_map]
  refine List.map_congr_left fun q _ => ?_
  simp only [Function.comp_apply, List.map_map]
  refine List.map_congr_left fun p _ => ?_
  exact bkOf_view p.2

theorem sorted_interA' {a : Array Nat} (ha : SortedA a) (b : Array Nat) : SortedA (interA a b) := by
  unfold SortedA interA
  rw [Array.toList_filter]
  exact ha.filter _

theorem sorted_foldl_interA' : ∀ (ts : List (Array Nat)) {t : Array Nat}, SortedA t →
    SortedA (ts.foldl interA t)
  | [], _, ht => ht
  | x :: ts, _, ht => by rw [List.foldl_cons]; exact sorted_foldl_interA' ts (sorted_interA' ht x)

theorem absTy_interA {a b : Array Nat} (hb : SortedA b) : absTy n (interA a b) = absTy n a ∩ absTy n b := by
  ext y
  rw [Finset.mem_inter, mem_absTy, mem_absTy, mem_absTy, interA, Array.mem_filter, bsA_iff hb]

theorem absTy_foldl_interA : ∀ (xs : List (Array Nat)) (x : Array Nat), (∀ X ∈ xs, SortedA X) →
    absTy n (xs.foldl interA x) = (xs.map (absTy n)).foldl (· ∩ ·) (absTy n x)
  | [], _, _ => rfl
  | y :: xs, x, h => by
    simp only [List.foldl_cons, List.map_cons]
    rw [absTy_foldl_interA xs _ fun X hX => h X (List.mem_cons_of_mem _ hX),
      absTy_interA (h y List.mem_cons_self)]

theorem absTy_interLA {l : List (Array Nat)} (h : ∀ X ∈ l, SortedA X) :
    absTy n (interLA l) = interL (l.map (absTy n)) := by
  cases l with
  | nil => exact absTy_empty
  | cons x xs =>
    simp only [interLA, interL, List.map_cons]
    exact absTy_foldl_interA xs x fun X hX => h X (List.mem_cons_of_mem _ hX)

theorem absTy_forcedA {cl : List (List (Array Nat))} (h : ∀ l ∈ cl, ∀ X ∈ l, SortedA X) :
    absTy n (forcedA cl) = forcedOf (cl.map (List.map (absTy n))) := by
  induction cl with
  | nil => exact absTy_empty
  | cons l cl ih =>
    have h1 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    simp only [forcedA, forcedOf, List.foldr_cons, List.map_cons] at h1 ⊢
    rw [absTy_unionA, h1, absTy_interLA (h l List.mem_cons_self)]

theorem mem_foldl_interA : ∀ (xs : List (Array Nat)) (x : Array Nat) (z : Nat),
    z ∈ xs.foldl interA x → z ∈ x
  | [], _, _, h => h
  | y :: xs, x, z, h => by
    rw [List.foldl_cons] at h
    exact (Array.mem_filter.1 (mem_foldl_interA xs _ z h)).1

theorem mem_forcedA : ∀ {cl : List (List (Array Nat))} {z : Nat}, z ∈ forcedA cl →
    ∃ l ∈ cl, ∃ X ∈ l, z ∈ X
  | [], z, h => by simp [forcedA] at h
  | l :: cl, z, h => by
    simp only [forcedA, List.foldr_cons] at h
    rcases mem_unionA.1 h with h | h
    · obtain ⟨l', hl', X, hX, hz⟩ := mem_forcedA (cl := cl) h
      exact ⟨l', List.mem_cons_of_mem _ hl', X, hX, hz⟩
    · cases l with
      | nil => simp [interLA] at h
      | cons x xs =>
        exact ⟨_, List.mem_cons_self, x, List.mem_cons_self, mem_foldl_interA xs x z h⟩

theorem sorted_interLA {l : List (Array Nat)} (h : ∀ X ∈ l, SortedA X) : SortedA (interLA l) := by
  cases l with
  | nil => simp [interLA, SortedA]
  | cons x xs =>
    simp only [interLA]
    exact sorted_foldl_interA' xs (h x List.mem_cons_self)

theorem sorted_forcedA {cl : List (List (Array Nat))} (h : ∀ l ∈ cl, ∀ X ∈ l, SortedA X) :
    SortedA (forcedA cl) := by
  induction cl with
  | nil => simp [forcedA, SortedA]
  | cons l cl ih =>
    simp only [forcedA, List.foldr_cons] at ih ⊢
    exact sorted_unionA (ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
      (sorted_interLA (h l List.mem_cons_self))

theorem mem_backListsA {v : NodeA} {κ : KeyA} {lows : List (Fin n × Nat × RoleT (Fin m) × Fin n)}
    {l : List (Array Nat)} (hl : l ∈ backListsA C v κ lows) {X : Array Nat} (hX : X ∈ l) :
    ∃ j, X = bkA C j := by
  simp only [backListsA, List.mem_map] at hl
  obtain ⟨q, -, rfl⟩ := hl
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hX
  exact ⟨_, rfl⟩

theorem backOKA_sound (hW : WF n m C) {i : Nat}
    (h : backOKA (mkIx O) C (ndA C i) (keyA C (ndA C i).ctx) (lowAtA (mkIx O) (ndA C i).ty) = true) :
    BackOK (mkIx O) (C.view n m) i := by
  unfold BackOK
  rw [backLists_view hW]
  set cl := backListsA C (ndA C i) (keyA C (ndA C i).ctx) (lowAtA (mkIx O) (ndA C i).ty) with hcl
  have hS : ∀ l ∈ cl, ∀ X ∈ l, SortedA X := fun l hl X hX => by
    obtain ⟨j, rfl⟩ := mem_backListsA hl hX; exact hW.bk j
  rw [← absTy_forcedA hS]
  intro hne
  have hne' : cl.all (fun l => !l.isEmpty) = true := by
    simp only [List.all_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]
    intro l hl
    exact hne _ (List.mem_map.2 ⟨l, hl, rfl⟩) ∘ fun h => by rw [h]; rfl
  simp only [backOKA, ← hcl] at h
  rw [if_pos hne'] at h
  rw [view_nd_ty, view_nd_ctx]
  by_cases hF : (forcedA cl).all (bsA (ndA C i).ty) = true
  · rw [if_pos hF] at h
    refine ⟨fun hn => absurd (fun y hy => ?_) hn, fun _ l' hl' X' hX' hnX => ?_⟩
    · rw [mem_absTy] at hy ⊢
      exact bsA_sound (all_mem hF hy)
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hl'
      obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hX'
      have hXn : X.all (bsA (ndA C i).ty) = false := by
        rw [Bool.eq_false_iff]
        intro hall
        exact hnX fun y hy => by
          rw [mem_absTy] at hy ⊢; exact bsA_sound (all_mem hall hy)
      have hXm : X ∈ (cl.flatMap id).filter fun X => !X.all (bsA (ndA C i).ty) :=
        List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨l, hl, hX⟩, by simp [hXn]⟩
      obtain ⟨Y, hY, hYX⟩ := exists_dedupKey id _ X hXm
      simp only [id] at hYX
      subst hYX
      have := List.all_eq_true.1 h Y hY
      have hc := brCovA_sound (sorted_unionA (hW.ty i) (hS l hl Y hX)) this
      rwa [absTy_unionA] at hc
  · rw [if_neg hF] at h
    refine ⟨fun _ => ?_, fun hsub => absurd hsub ?_⟩
    · have hc := brCovA_sound (sorted_unionA (hW.ty i) (sorted_forcedA hS)) h
      rwa [absTy_unionA] at hc
    · intro hsub
      rw [Bool.not_eq_true, Bool.eq_false_iff] at hF
      apply hF
      rw [← Array.all_toList, List.all_eq_true]
      intro z hz
      obtain ⟨l, hl, X, hX, hzX⟩ := mem_forcedA (Array.mem_def.2 hz)
      obtain ⟨j, rfl⟩ := mem_backListsA hl hX
      have hzn := hW.bkB j z hzX
      have := hsub (mem_absTy (y := ⟨z, hzn⟩) |>.2 (Array.mem_def.2 hz))
      exact (bsA_iff (hW.ty i)).2 (mem_absTy.1 this)

end Back

/-! ## The merge rule -/

section Merge

variable {O : Ontology (Fin n) (Fin m)} {C : CandA}

theorem decide_eq_of_iff {P : Prop} [Decidable P] {b : Bool} (h : P ↔ b = true) : decide P = b := by
  cases b <;> simp_all

theorem cset_view (hW : WF n m C) (i : Nat) (S : RoleT (Fin m)) (e : Fin n) :
    cset (C.view n m) i S e = (csetA C (ndA C i) S e).map (viewEntry n m) := by
  simp only [cset, csetA, view_nd_pool, List.filter_map]
  congr 1
  refine List.filter_congr fun σ hσ => decide_eq_of_iff ?_
  simp only [viewEntry, uniOf_view, Bool.and_eq_true, mem_absLab, mem_absTy,
    bsA_iff (hW.ent i σ hσ).1, bsA_iff (hW.uni _)]

theorem potOf_view (hW : WF n m C) (i : Nat) {Cs : List EntryA} (hCs : ∀ σ ∈ Cs, SortedA σ.lab)
    (pc : Nat) :
    potOf (mkIx O) (C.view n m) i (Cs.map (viewEntry n m)) pc =
      potOfA C (lowAtA (mkIx O) (ndA C i).ty) Cs pc := by
  simp only [potOf, potOfA, view_nd_ty, ← lowAtA_eq _ (hW.ty i)]
  congr 3
  refine List.filter_congr fun q _ => decide_eq_of_iff ?_
  simp only [List.mem_map, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, h1, h2⟩
    simp only [viewEntry, uniOf_view, mem_absLab, mem_absTy] at h1 h2
    exact ⟨σ, hσ, (bsA_iff (hCs σ hσ)).2 h1, (bsA_iff (hW.uni _)).2 h2⟩
  · rintro ⟨σ, hσ, h1, h2⟩
    refine ⟨_, ⟨σ, hσ, rfl⟩, ?_, ?_⟩
    · simp only [viewEntry, mem_absLab]; exact (bsA_iff (hCs σ hσ)).1 h1
    · simp only [viewEntry, uniOf_view, mem_absTy]; exact (bsA_iff (hW.uni _)).1 h2

theorem csetA_sub {v : NodeA} {S : RoleT (Fin m)} {e : Fin n} {σ : EntryA} (h : σ ∈ csetA C v S e) :
    σ ∈ v.pool := (List.mem_filter.1 h).1

theorem pot_view (hW : WF n m C) (i : Nat) (S : RoleT (Fin m)) (e : Fin n) :
    pot (mkIx O) (C.view n m) i S e =
      potA C (ndA C i) (keyA C (ndA C i).ctx) (lowAtA (mkIx O) (ndA C i).ty) S e := by
  simp only [pot, potA, cset_view hW, view_key_ctx]
  rw [potOf_view hW i (fun σ hσ => (hW.ent i σ (csetA_sub hσ)).1), pcBA_eq (hW.lab _) (hW.pi _)]

theorem spec_eq_dflt (hW : WF n m C) {i : Nat} {σ : EntryA} (hσ : σ ∈ (ndA C i).pool)
    (q : Fin n × Nat × RoleT (Fin m) × Fin n) :
    (viewEntry n m σ).spec = dflt (mkIx O) q ↔
      σ.lab = upSA (mkIxF O (mkIx O)) q.2.2.1 ∧ σ.fill = #[q.2.2.2.val] := by
  obtain ⟨hl, hlb, hf, hfb⟩ := hW.ent i σ hσ
  simp only [viewEntry, dflt, Spec.mk.injEq, ← absLab_upSA (O := O) (ix := mkIx O),
    ← absTy_single]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨absLab_inj hl (sorted_upSA _) hlb (bnd_upSA _) h1, ?_⟩
    refine absTy_inj hf (by simp [SortedA]) hfb (by simp) h2
  · rintro ⟨h1, h2⟩
    rw [h1, h2]
    exact ⟨rfl, rfl⟩

theorem ddef_view (hW : WF n m C) (i : Nat) (S : RoleT (Fin m)) (e : Fin n) :
    ddef (mkIx O) (C.view n m) i S e =
      (ddefA (mkIx O) (mkIxF O (mkIx O)) C (ndA C i) (keyA C (ndA C i).ctx)
        (lowAtA (mkIx O) (ndA C i).ty) S e).map (viewSpec n m) := by
  simp only [ddef, ddefA, cset_view hW, List.filter_map, List.map_map]
  congr 1
  · refine List.filter_congr fun σ hσ => decide_eq_of_iff ?_
    have hσp := csetA_sub hσ
    simp only [Bool.and_eq_true,
      Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true', view_nd_ty, view_nd_ctx,
      ← lowAtA_eq _ (hW.ty i), keyOf_view]
    refine and_congr ?_ ?_
    · constructor
      · rintro ⟨q, hq, hk, hs, he⟩
        refine ⟨q, hq, ⟨⟨⟨by simpa using hk, ?_⟩, ?_⟩, ?_⟩⟩
        · rw [Bool.eq_false_iff]; intro h; exact hs ((skipQA_iff (hW.lab _) (hW.pi _) q).1 h)
        · simpa using ((spec_eq_dflt hW hσp q).1 he).1
        · simpa using ((spec_eq_dflt hW hσp q).1 he).2
      · rintro ⟨q, hq, ⟨⟨hk, hs⟩, h1⟩, h2⟩
        refine ⟨q, hq, by simpa using hk, fun h => ?_, (spec_eq_dflt hW hσp q).2 ⟨by simpa using h1,
          by simpa using h2⟩⟩
        rw [← skipQA_iff (hW.lab _) (hW.pi _) q, hs] at h
        exact Bool.false_ne_true h
    · simp only [viewKey, viewEntry, mem_absTy, bsA_iff (hW.seed _), decide_eq_true_iff]

theorem viewSpec_specUnionA : ∀ l : List (Array Nat × Array Nat),
    viewSpec n m (specUnionA l) = specUnion (l.map (viewSpec n m))
  | [] => by
    simp only [specUnionA, List.flatMap_nil, List.map_nil, specUnion, List.foldr_nil, viewSpec,
      Spec.mk.injEq]
    exact ⟨by ext R; simp [mem_absLab, mem_canon], by ext y; simp [mem_absTy, mem_canon]⟩
  | x :: l => by
    have ih := viewSpec_specUnionA l
    simp only [List.map_cons, specUnion, List.foldr_cons] at ih ⊢
    rw [← ih]
    simp only [specUnionA, viewSpec, Spec.union, Spec.mk.injEq]
    constructor
    · ext R
      rw [mem_absLab, Finset.mem_union, mem_absLab, mem_absLab, mem_canon, mem_canon,
        List.flatMap_cons, List.mem_append, Array.mem_def]
    · ext y
      rw [mem_absTy, Finset.mem_union, mem_absTy, mem_absTy, mem_canon, mem_canon,
        List.flatMap_cons, List.mem_append, Array.mem_def]

theorem viewSpec_unionS (a b : Array Nat × Array Nat) :
    viewSpec n m (unionS a b) = (viewSpec n m a).union (viewSpec n m b) := by
  simp only [viewSpec, unionS, Spec.union, absLab_unionA, absTy_unionA]

theorem leS_of_le {M σ : Array Nat × Array Nat} (hM1 : ∀ x ∈ M.1, x < 2 * m) (hM2 : ∀ x ∈ M.2, x < n)
    (hs1 : SortedA σ.1) (hs2 : SortedA σ.2) (h : (viewSpec n m M).le (viewSpec n m σ)) :
    leS M σ = true := by
  simp only [viewSpec, Spec.le] at h
  simp only [leS, Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · rw [← Array.all_toList, List.all_eq_true]
    intro x hx
    have hx' := hM1 x (Array.mem_def.2 hx)
    have := h.1 ((mem_absLab (R := ofRc x hx')).2 (by rw [rc_ofRc]; exact Array.mem_def.2 hx))
    rw [mem_absLab, rc_ofRc] at this
    exact (bsA_iff hs1).2 this
  · rw [← Array.all_toList, List.all_eq_true]
    intro x hx
    have hx' := hM2 x (Array.mem_def.2 hx)
    have := h.2 ((mem_absTy (y := ⟨x, hx'⟩)).2 (Array.mem_def.2 hx))
    exact (bsA_iff hs2).2 (mem_absTy.1 this)

theorem mergeCoreA_sound (hW : WF n m C) {i k : Nat} {Cs : List EntryA} (hCs : ∀ σ ∈ Cs, σ ∈ (ndA C i).pool)
    {hasD : Bool} {M : Array Nat × Array Nat} (hM1 : ∀ x ∈ M.1, x < 2 * m) (hM2 : ∀ x ∈ M.2, x < n)
    (h : mergeCoreA (poolSet (ndA C i)) k Cs hasD M = true) :
    mergeCore (C.view n m) i k (Cs.map (viewEntry n m)) hasD (viewSpec n m M) := by
  have hv : ∀ σ : EntryA, (viewEntry n m σ).spec = viewSpec n m (σ.lab, σ.fill) := fun _ => rfl
  have hin : ∀ p : Array Nat × Array Nat, (poolSet (ndA C i)).contains p = true →
      inPool (C.view n m) i (viewSpec n m p) := fun p hp => poolSet_sound hp
  have hle : ∀ σ ∈ Cs, (viewSpec n m M).le (viewEntry n m σ).spec → leS M (σ.lab, σ.fill) = true :=
    fun σ hσ hl => leS_of_le hM1 hM2 (hW.ent i σ (hCs σ hσ)).1 (hW.ent i σ (hCs σ hσ)).2.2.1 hl
  unfold mergeCore
  unfold mergeCoreA at h
  dsimp only at h
  split
  · next hk =>
    rw [if_pos hk] at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_map, Bool.or_eq_true,
      Bool.not_eq_true', forall_exists_index, and_imp] at h
    refine ⟨fun σ0 hσ0 => ?_, fun σ01 hσ01 σ02 hσ02 h1 h2 => ?_⟩
    · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hσ0
      rw [hv, ← viewSpec_unionS]
      exact hin _ (h.1 _ σ hσ rfl)
    · obtain ⟨σ₁, hσ₁, rfl⟩ := List.mem_map.1 hσ01
      obtain ⟨σ₂, hσ₂, rfl⟩ := List.mem_map.1 hσ02
      rw [hv, hv, ← viewSpec_unionS]
      rcases h.2 _ σ₁ hσ₁ rfl _ σ₂ hσ₂ rfl with (h' | h') | h'
      · rw [hle σ₁ hσ₁ h1] at h'; exact Bool.noConfusion h'
      · rw [hle σ₂ hσ₂ h2] at h'; exact Bool.noConfusion h'
      · exact hin _ h'
  · next hk =>
    rw [if_neg hk] at h
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp] at h
    intro σ01 hσ01 σ02 hσ02
    obtain ⟨σ₁, hσ₁, rfl⟩ := List.mem_map.1 hσ01
    obtain ⟨σ₂, hσ₂, rfl⟩ := List.mem_map.1 hσ02
    rw [hv, hv, ← viewSpec_unionS]
    exact hin _ (h _ σ₁ hσ₁ rfl _ σ₂ hσ₂ rfl)

theorem specUnionA_bnd {i : Nat} (hW : WF n m C) {l : List (Array Nat × Array Nat)}
    (hl : ∀ p ∈ l, ∃ σ ∈ (ndA C i).pool, p = (σ.lab, σ.fill)) :
    (∀ x ∈ (specUnionA l).1, x < 2 * m) ∧ ∀ x ∈ (specUnionA l).2, x < n := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [specUnionA, mem_canon, List.mem_flatMap] at hx
    obtain ⟨p, hp, hx⟩ := hx
    obtain ⟨σ, hσ, rfl⟩ := hl p hp
    exact (hW.ent i σ hσ).2.1 x (Array.mem_def.2 hx)
  · simp only [specUnionA, mem_canon, List.mem_flatMap] at hx
    obtain ⟨p, hp, hx⟩ := hx
    obtain ⟨σ, hσ, rfl⟩ := hl p hp
    exact (hW.ent i σ hσ).2.2.2 x (Array.mem_def.2 hx)

theorem r5A_sound (hW : WF n m C) {i : Nat}
    (h : r5A (mkIx O) (mkIxF O (mkIx O)) C (ndA C i) (keyA C (ndA C i).ctx)
      (lowAtA (mkIx O) (ndA C i).ty) (uppAtA (mkIx O) (ndA C i).ty) (poolSet (ndA C i)) = true) :
    ∀ u ∈ uppAt (mkIx O) (nd (C.view n m) i).ty, u.2.1 < pot (mkIx O) (C.view n m) i u.2.2.1 u.2.2.2 →
      MergeOK (mkIx O) (C.view n m) i u.2.1 u.2.2.1 u.2.2.2 := by
  intro u hu hk
  rw [view_nd_ty, ← uppAtA_eq _ (hW.ty i)] at hu
  rw [pot_view hW] at hk
  simp only [r5A, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
  rcases h u hu with h | h
  · exact absurd hk h
  · unfold MergeOK
    rw [cset_view hW, ddef_view hW, List.isEmpty_map, ← viewSpec_specUnionA]
    have hD : ∀ p ∈ ddefA (mkIx O) (mkIxF O (mkIx O)) C (ndA C i) (keyA C (ndA C i).ctx)
        (lowAtA (mkIx O) (ndA C i).ty) u.2.2.1 u.2.2.2, ∃ σ ∈ (ndA C i).pool, p = (σ.lab, σ.fill) := by
      intro p hp
      simp only [ddefA, List.mem_map, List.mem_filter] at hp
      obtain ⟨σ, ⟨hσ, -⟩, rfl⟩ := hp
      exact ⟨σ, csetA_sub hσ, rfl⟩
    obtain ⟨hb1, hb2⟩ := specUnionA_bnd hW hD
    exact mergeCoreA_sound hW (fun σ hσ => csetA_sub hσ) hb1 hb2 h

end Merge

/-! ## The parent-witness rule -/

section Wit

variable {O : Ontology (Fin n) (Fin m)} {C : CandA}

theorem mem_witA (hW : WF n m C) {j : Nat} {u : Fin n × Nat × RoleT (Fin m) × Fin n}
    (hu : u ∈ uppAt (mkIx O) (nd (C.view n m) j).ty)
    (hpc : pcB (keyOf (C.view n m) (nd (C.view n m) j).ctx) u.2.2.1 u.2.2.2 = 1)
    (hk : u.2.1 < pot (mkIx O) (C.view n m) j u.2.2.1 u.2.2.2)
    {σ : Entry n m} (hσ : σ ∈ cset (C.view n m) j u.2.2.1 u.2.2.2) :
    ∃ σA ∈ csetA C (ndA C j) u.2.2.1 u.2.2.2, σ = viewEntry n m σA ∧
      (σA.lab, σA.fill) ∈ witA (mkIx O) C j := by
  rw [cset_view hW] at hσ
  obtain ⟨σA, hσA, rfl⟩ := List.mem_map.1 hσ
  refine ⟨σA, hσA, rfl, ?_⟩
  rw [view_nd_ty, ← uppAtA_eq _ (hW.ty j)] at hu
  rw [view_key_ctx, ← pcBA_eq (hW.lab _) (hW.pi _)] at hpc
  rw [pot_view hW] at hk
  simp only [witA]
  rw [if_neg (by rw [List.isEmpty_iff]; exact List.ne_nil_of_mem hu)]
  simp only [List.mem_flatMap]
  refine ⟨u, hu, ?_⟩
  rw [if_pos ⟨hpc, hk⟩]
  exact List.mem_map.2 ⟨σA, hσA, rfl⟩

theorem witOKA_sound (hW : WF n m C) {i : Nat}
    (h : witOKA (mkIx O) C (witArr (mkIx O) C) (ndA C i) (poolSet (ndA C i)) = true) :
    WitOK (mkIx O) (C.view n m) i := by
  intro e he j hj u hu hpc hk σ hσ
  rw [view_nd_pool] at he
  obtain ⟨eA, heA, rfl⟩ := List.mem_map.1 he
  rw [memb_view] at hj
  obtain ⟨hjn, hjc⟩ := mem_membA hj
  have hpc' : pcB (keyOf (C.view n m) (nd (C.view n m) j).ctx) u.2.2.1 u.2.2.2 = 1 := by
    rw [view_nd_ctx, hjc]; exact hpc
  obtain ⟨σA, hσA, rfl, hw⟩ := mem_witA hW hu hpc' hk hσ
  have hσp := csetA_sub hσA
  obtain ⟨-, -, hfs, hfb⟩ := hW.ent j σA hσp
  have hWj : (witArr (mkIx O) C)[j]?.getD [] = witA (mkIx O) C j := by
    simp [witArr, Array.getElem?_ofFn, hjn]
  have hr : (eA, (σA.lab, σA.fill)) ∈ (ndA C i).pool.flatMap fun e =>
      (membA C e.kid).flatMap fun j => ((witArr (mkIx O) C)[j]?.getD []).map fun σ => (e, σ) :=
    List.mem_flatMap.2 ⟨eA, heA, List.mem_flatMap.2 ⟨j, hj, by rw [hWj]; exact List.mem_map.2 ⟨_, hw, rfl⟩⟩⟩
  simp only [witOKA, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [view_nd_ty, view_nd_ctx]
  have hiff : (viewEntry n m σA).spec.fill ⊆ absTy n (ndA C i).ty ↔ σA.fill.all (bsA (ndA C i).ty) = true := by
    simp only [viewEntry]
    constructor
    · intro hsub
      rw [← Array.all_toList, List.all_eq_true]
      intro x hx
      have := hsub ((mem_absTy (y := ⟨x, hfb x (Array.mem_def.2 hx)⟩)).2 (Array.mem_def.2 hx))
      exact (bsA_iff (hW.ty i)).2 (mem_absTy.1 this)
    · intro hall y hy
      rw [mem_absTy] at hy ⊢
      exact bsA_sound (all_mem hall hy)
  refine ⟨fun hsub => ?_, fun hns => ?_⟩
  · have hm : (unionA eA.lab (flipA σA.lab), eA.fill) ∈ (List.filter (fun r => r.2.2.all (bsA (ndA C i).ty))
        ((ndA C i).pool.flatMap fun e => (membA C e.kid).flatMap fun j =>
          ((witArr (mkIx O) C)[j]?.getD []).map fun σ => (e, σ))).map fun r =>
            (unionA r.1.lab (flipA r.2.1), r.1.fill) :=
      List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hr, (hiff.1 hsub)⟩, rfl⟩
    obtain ⟨y, hy, hyx⟩ := exists_dedupKey id _ _ hm
    simp only [id] at hyx
    subst hyx
    have := poolSet_sound (n := n) (m := m) (h1 _ hy)
    simp only [viewEntry, grown, absLab_unionA, absLab_flipA] at this ⊢
    exact this
  · have hm : σA.fill ∈ (List.filter (fun r => !r.2.2.all (bsA (ndA C i).ty))
        ((ndA C i).pool.flatMap fun e => (membA C e.kid).flatMap fun j =>
          ((witArr (mkIx O) C)[j]?.getD []).map fun σ => (e, σ))).map (·.2.2) :=
      List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hr, by
        rw [Bool.not_eq_true']; rw [Bool.eq_false_iff]; exact fun hc => hns (hiff.2 hc)⟩, rfl⟩
    obtain ⟨y, hy, hyx⟩ := exists_dedupKey id _ _ hm
    simp only [id] at hyx
    subst hyx
    have := brCovA_sound (sorted_unionA (hW.ty i) hfs) (h2 _ hy)
    rw [absTy_unionA] at this
    exact this

end Wit

/-! ## The whole check -/

section Main

variable {O : Ontology (Fin n) (Fin m)} {C : CandA}

theorem nodeClosedA_sound (hW : WF n m C) {i : Nat}
    (h : nodeClosedA (mkIx O) (mkIxF O (mkIx O)) C (witArr (mkIx O) C) i = true) :
    NodeClosed (mkIx O) (C.view n m) i := by
  simp only [nodeClosedA, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨nodeOKA_sound hW h1, fun e he => ?_, r3A_sound hW h3, backOKA_sound hW h4,
    r5A_sound hW h5, witOKA_sound hW h6⟩
  rw [view_nd_pool] at he
  obtain ⟨eA, heA, rfl⟩ := List.mem_map.1 he
  exact entryOKA_sound hW heA (List.all_eq_true.1 h2 eA heA)

theorem rootOKA_sound (hW : WF n m C) {a : Fin n} {k : Nat}
    (h : rootOKA (mkIx O) C a k = true) : RootOK (mkIx O) (C.view n m) a k := by
  simp only [rootOKA, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by simpa using h1, ?_, ?_⟩
  · rw [keyOf_view, h2]
    simp only [viewKey, absTy_single, absLab_empty, absTy_empty]
  · have := brCovA_sound (n := n) (m := m) (by simp [SortedA]) h3
    rwa [absTy_single] at this

theorem mem_foldr_union {l : List Nat} {f : Nat → Ty n} {y : Fin n} :
    y ∈ l.foldr (fun j acc => f j ∪ acc) ∅ ↔ ∃ j ∈ l, y ∈ f j := by
  induction l with
  | nil => simp
  | cons j l ih => simp [ih]

theorem mem_foldl_unionA {f : Nat → Array Nat} : ∀ (l : List Nat) (acc : Array Nat) (z : Nat),
    z ∈ l.foldl (fun acc j => unionA acc (f j)) acc ↔ z ∈ acc ∨ ∃ j ∈ l, z ∈ f j
  | [], acc, z => by simp
  | j :: l, acc, z => by
    rw [List.foldl_cons, mem_foldl_unionA l _ z, mem_unionA]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem cacheOKA_sound (hW : WF n m C) (h : cacheOKA (mkIx O) C = true) :
    CacheOK (mkIx O) (C.view n m) := by
  simp only [cacheOKA, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun j hj => ?_, fun k hk => ?_⟩
  · rw [view_nodes_size] at hj
    rw [bkOf_view, h1 j hj, absTy_canon_fwd' _ (hW.lab _), backOf, view_nd_ty, view_key_ctx]
    rfl
  · rw [view_keys_size] at hk
    rw [uniOf_view, h2 k hk, memb_view]
    ext y
    rw [mem_absTy, mem_foldl_unionA, mem_foldr_union]
    simp only [view_nd_ty, mem_absTy, Array.mem_def, List.not_mem_nil, false_or]

/-- **The fast check is sound**: when it accepts, the finset candidate set
the arrays denote satisfies the closure conditions. -/
theorem closedFastB_sound {req : List (Fin n)}
    (h : closedFastB (mkIx O) (mkIxF O (mkIx O)) C req = true) :
    ClosedP (mkIx O) (C.view n m) req := by
  simp only [closedFastB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨hw, hlen⟩, hroot⟩, hr2⟩, hnodes⟩, hcache⟩ := h
  have hW := wfB_sound hw
  refine ⟨by simpa using hlen, fun p hp => ?_, fun k hk => ?_, fun i hi => ?_, cacheOKA_sound hW hcache⟩
  · rw [view_roots] at hp
    exact rootOKA_sound hW (hroot p hp)
  · rw [view_keys_size] at hk
    rw [keyOf_view]
    exact brCovA_sound (hW.seed k) (hr2 k hk)
  · rw [view_nodes_size] at hi
    exact nodeClosedA_sound hW (hnodes i hi)

end Main

end ContextCalculus.SRIQ.Fast

#print axioms ContextCalculus.SRIQ.Fast.closedFastB_sound
