import ContextCalculus.SRIQ.FastBasic

/-!
# Certificate check for the fast SHIQ procedure: soundness (stage C1c)

For every candidate set `U`, without the closure check:

- `suppB_iff`: the executable support test is the support condition
  `SuppP` (a list of entries among the live nodes meets every clause at
  the node with the parent entry);
- `elim_spec`: the elimination keeps exactly a greatest self-supporting
  set of nodes (`al_supp`, `subset_al`);
- `recs_selfSupp`: the records of the live nodes (a root record for each
  live node of a context with an empty label, and a child record for each
  entry used by a live node) support themselves in the sense of
  `Stars.lean`, so the live root types are good (`al_good`);
- `fastRows_sound`: a listed row is satisfiable and contains every
  subsumer.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat} {O : Ontology (Fin n) (Fin m)}

/-! ## Support -/

section Support

variable (O) (U : Cand n m)

/-- An entry of node `i` among the nodes `A`: a checked pool entry and a
node of its child context in `A` whose back set `i` holds. -/
def CandP (A : Nat → Prop) (i : Nat) (c : Lab m × Ty n) : Prop :=
  ∃ e ∈ (nd U i).pool, entryOK (mkIx O) U (nd U i).ty e ∧ ∃ j ∈ memb U e.kid, A j ∧
    backOf (mkIx O) U j ⊆ (nd U i).ty ∧ c = (e.spec.lab, (nd U j).ty)

/-- Node `i` is supported among the nodes `A`. -/
def SuppP (A : Nat → Prop) (i : Nat) : Prop :=
  nodeOK (mkIx O) U i ∧ limsOK (mkIx O) U i ∧ ∃ E : List (Lab m × Ty n), (∀ c ∈ E, CandP O U A i c) ∧
    (∀ q ∈ lowAt (mkIx O) (nd U i).ty, q.2.1 ≤
      pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2 + E.countP (cntP q.2.2.1 q.2.2.2)) ∧
    (∀ u ∈ uppAt (mkIx O) (nd U i).ty,
      pcB (keyOf U (nd U i).ctx) u.2.2.1 u.2.2.2 + E.countP (cntP u.2.2.1 u.2.2.2) ≤ u.2.1)

variable {O U}

theorem candP_mono {A B : Nat → Prop} (hAB : ∀ j, A j → B j) {i : Nat} {c : Lab m × Ty n}
    (h : CandP O U A i c) : CandP O U B i c := by
  obtain ⟨e, he, hok, j, hj, hA, hb, rfl⟩ := h
  exact ⟨e, he, hok, j, hj, hAB j hA, hb, rfl⟩

theorem suppP_mono {A B : Nat → Prop} (hAB : ∀ j, A j → B j) {i : Nat} (h : SuppP O U A i) :
    SuppP O U B i := by
  obtain ⟨h1, h2, E, hE, h3, h4⟩ := h
  exact ⟨h1, h2, E, fun c hc => candP_mono hAB (hE c hc), h3, h4⟩

theorem nodeOK_lt {i : Nat} (h : nodeOK (mkIx O) U i) : i < U.nodes.size := h.1

theorem okArr_iff {i : Nat} :
    (okArr (mkIx O) U)[i]?.getD false = true ↔ nodeOK (mkIx O) U i := by
  simp only [okArr, Array.getElem?_ofFn]
  split
  · simp
  · next h =>
    simp only [Option.getD_none, Bool.false_eq_true, false_iff]
    exact fun h' => h h'.1

theorem mem_vpool {i : Nat} {e : Entry n m} :
    e ∈ vpool (mkIx O) U i ↔ e ∈ (nd U i).pool ∧ entryOK (mkIx O) U (nd U i).ty e := by
  simp only [vpool, vpools, getL, Array.getElem?_map, nd]
  cases U.nodes[i]? with
  | none => simp [default]
  | some ν => simp

theorem mem_memb {k j : Nat} (h : j ∈ memb U k) : j < U.nodes.size ∧ (nd U j).ctx = k := by
  simp only [memb, List.mem_filter, decide_eq_true_eq] at h
  exact h.2

theorem backG_eq {j : Nat} (h : j < U.nodes.size) : backG (mkIx O) U j = backOf (mkIx O) U j := by
  simp [backG, backs, Array.getElem?_ofFn, h]

theorem mem_candsA {A : Array Bool} {i : Nat} {c : Lab m × Ty n} :
    c ∈ candsA U (mkCache (mkIx O) U) A i ↔ CandP O U (fun j : Nat => A[j]? = some true) i c := by
  have h1 : getL (mkCache (mkIx O) U).vp i = vpool (mkIx O) U i := rfl
  have h2 : ∀ j, (mkCache (mkIx O) U).bk[j]?.getD ∅ = backG (mkIx O) U j := fun _ => rfl
  simp only [candsA, h1, h2, List.mem_flatMap, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq, mem_vpool, CandP]
  constructor
  · rintro ⟨e, ⟨he, hok⟩, j, ⟨hj, hA, hb⟩, rfl⟩
    refine ⟨e, he, hok, j, hj, ?_, ?_, rfl⟩
    · revert hA; cases A[j]? <;> simp
    · rwa [backG_eq (mem_memb hj).1] at hb
  · rintro ⟨e, he, hok, j, hj, hA, hb, rfl⟩
    refine ⟨e, ⟨he, hok⟩, j, ⟨hj, by simp [hA], ?_⟩, rfl⟩
    rwa [backG_eq (mem_memb hj).1]

theorem sol_iff {i : Nat} (hl : limsOK (mkIx O) U i) {E : List (Lab m × Ty n)} :
    Sol E (needsV (mkIx O) U i) (limsV (mkIx O) U i) ↔
      (∀ q ∈ lowAt (mkIx O) (nd U i).ty, q.2.1 ≤
        pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2 + E.countP (cntP q.2.2.1 q.2.2.2)) ∧
      (∀ u ∈ uppAt (mkIx O) (nd U i).ty,
        pcB (keyOf U (nd U i).ctx) u.2.2.1 u.2.2.2 + E.countP (cntP u.2.2.1 u.2.2.2) ≤ u.2.1) := by
  simp only [Sol, needsV, limsV, List.mem_map, forall_exists_index, and_imp]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun q hq => ?_, fun u hu => ?_⟩
    · have := h1 _ q hq rfl; simp only at this; omega
    · have := h2 _ u hu rfl; have := hl u hu; simp only at *; omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun x q hq hx => ?_, fun y u hu hy => ?_⟩
    · subst hx; have := h1 q hq; simp only; omega
    · subst hy; have := h2 u hu; simp only; omega

/-- **The support test is exact.** -/
theorem suppB_iff {A : Array Bool} {i : Nat} :
    suppB (mkIx O) U (mkCache (mkIx O) U) A i = true ↔ SuppP O U (fun j : Nat => A[j]? = some true) i := by
  have hok : (mkCache (mkIx O) U).ok = okArr (mkIx O) U := rfl
  simp only [suppB, hok, Bool.and_eq_true, decide_eq_true_eq, okArr_iff]
  constructor
  · rintro ⟨⟨hok, hl⟩, hd⟩
    obtain ⟨E, hE, hS⟩ := dfs_sound _ _ _ hd
    refine ⟨hok, hl, E, fun c hc => ?_, (sol_iff hl).1 hS⟩
    exact mem_candsA.1 (dedupKey_subset _ _ c (hE c hc))
  · rintro ⟨hok, hl, E, hE, hlow, hupp⟩
    refine ⟨⟨hok, hl⟩, ?_⟩
    obtain ⟨E', hE', h2, h3⟩ := sol_dedup (cs := candsA U (mkCache (mkIx O) U) A i)
      (needs := needsV (mkIx O) U i) (lims := limsV (mkIx O) U i) E
      (fun c hc => mem_candsA.2 (hE c hc))
    have hS : Sol E (needsV (mkIx O) U i) (limsV (mkIx O) U i) := (sol_iff hl).2 ⟨hlow, hupp⟩
    refine dfs_complete _ _ _ E' hE' ⟨fun x hx => ?_, fun y hy => ?_⟩ (Nat.lt_succ_self _)
    · rw [h2 x hx]; exact hS.1 x hx
    · rw [h3 y hy]; exact hS.2 y hy

end Support

/-! ## Elimination -/

section Elim

variable {U : Cand n m}

theorem leA_antisymm {A B : Array Bool} (h1 : LeA A B) (h2 : LeA B A) : A = B := by
  refine Array.ext_getElem? fun j => ?_
  by_cases hj : j < A.size
  · have hjB : j < B.size := h1.1 ▸ hj
    rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_getElem hjB]
    have a1 := h1.2 j
    have a2 := h2.2 j
    rw [Array.getElem?_eq_getElem hj, Array.getElem?_eq_getElem hjB] at a1 a2
    simp only [Option.some.injEq] at a1 a2 ⊢
    cases hA : A[j] <;> cases hB : B[j] <;> simp_all
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by have := h1.1; omega)]

theorem prune_sub {A : Array Bool} {i : Nat}
    (h : (prune (mkIx O) U (mkCache (mkIx O) U) A)[i]? = some true) : A[i]? = some true :=
  (foldl_sweep_le (mkIx O) U _ _ A).2 i h

theorem prune_fix_aux : ∀ (l : List Nat) (A : Array Bool),
    l.foldl (sweepStep (mkIx O) U (mkCache (mkIx O) U)) A = A →
    ∀ i ∈ l, A[i]? = some true → suppB (mkIx O) U (mkCache (mkIx O) U) A i = true
  | [], _, _, i, hi, _ => by simp at hi
  | j :: l, A, hfix, i, hi, hA => by
    rw [List.foldl_cons] at hfix
    have hle1 := sweepStep_le (mkIx O) U (mkCache (mkIx O) U) A j
    have hle2 := foldl_sweep_le (mkIx O) U (mkCache (mkIx O) U) l
      (sweepStep (mkIx O) U (mkCache (mkIx O) U) A j)
    rw [hfix] at hle2
    have heq := leA_antisymm hle1 hle2
    rw [heq] at hfix
    rcases List.mem_cons.1 hi with rfl | hi
    · have hlt : i < A.size := by
        by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hA; simp at hA
      have := congrArg (fun B : Array Bool => B[i]?) heq
      simp only [sweepStep, hA, Option.getD_some, if_true, Array.set!,
        Array.getElem?_setIfInBounds, hlt] at this
      simpa [hA] using this
    · exact prune_fix_aux l A hfix i hi hA

theorem prune_keep {S : Nat → Prop} (hsup : ∀ i, S i → SuppP O U S i) :
    ∀ (l : List Nat) (A : Array Bool), (∀ i : Nat, S i → A[i]? = some true) →
    ∀ i : Nat, S i → (l.foldl (sweepStep (mkIx O) U (mkCache (mkIx O) U)) A)[i]? = some true
  | [], A, hS => hS
  | j :: l, A, hS => by
    rw [List.foldl_cons]
    refine prune_keep hsup l _ fun i hi => ?_
    unfold sweepStep
    split
    · rw [Array.set!, Array.getElem?_setIfInBounds]
      split
      · next hij =>
        subst hij
        have hA := hS j hi
        have hlt : j < A.size := by
          by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hA; simp at hA
        rw [if_pos hlt, suppB_iff.2 (suppP_mono (fun k hk => hS k hk) (hsup j hi))]
      · exact hS i hi
    · exact hS i hi

theorem elim_spec : ∀ A : Array Bool,
    (∀ i : Nat, (elim (mkIx O) U (mkCache (mkIx O) U) A)[i]? = some true → A[i]? = some true) ∧
    (∀ i : Nat, (elim (mkIx O) U (mkCache (mkIx O) U) A)[i]? = some true →
      suppB (mkIx O) U (mkCache (mkIx O) U) (elim (mkIx O) U (mkCache (mkIx O) U) A) i = true) ∧
    (∀ S : Nat → Prop, (∀ i : Nat, S i → A[i]? = some true) → (∀ i, S i → SuppP O U S i) →
      ∀ i : Nat, S i → (elim (mkIx O) U (mkCache (mkIx O) U) A)[i]? = some true) := by
  intro A
  induction h : trues A using Nat.strong_induction_on generalizing A with
  | _ k ih =>
    rw [elim]
    split
    · next hp =>
      refine ⟨fun i hi => hi, fun i hi => ?_, fun S hS _ i hi => hS i hi⟩
      have hlt : i < A.size := by
        by_contra hn; rw [Array.getElem?_eq_none (by omega)] at hi; simp at hi
      exact prune_fix_aux (O := O) (U := U) (List.range A.size).reverse A hp i
        (List.mem_reverse.2 (List.mem_range.2 hlt)) hi
    · next hp =>
      obtain ⟨h1, h2, h3⟩ := ih _ (h ▸ trues_prune_lt (mkIx O) U hp)
        (prune (mkIx O) U (mkCache (mkIx O) U) A) rfl
      refine ⟨fun i hi => prune_sub (h1 i hi), h2, fun S hS hsup => h3 S (fun i hi => ?_) hsup⟩
      exact prune_keep hsup _ A hS i hi

variable (O U) in
/-- The live nodes. -/
def Al (i : Nat) : Prop := (aliveArr (mkIx O) U)[i]? = some true

theorem al_supp {i : Nat} (h : Al O U i) : SuppP O U (Al O U) i :=
  suppB_iff.1 ((elim_spec (O := O) (U := U) _).2.1 i h)

theorem al_nodeOK {i : Nat} (h : Al O U i) : nodeOK (mkIx O) U i := (al_supp h).1

/-- **Greatest.** Every self-supporting set of checked nodes is live. -/
theorem subset_al {S : Nat → Prop} (hS : ∀ i, S i → nodeOK (mkIx O) U i)
    (hsup : ∀ i, S i → SuppP O U S i) {i : Nat} (hi : S i) : Al O U i := by
  refine (elim_spec (O := O) (U := U) _).2.2 S (fun j hj => ?_) hsup i hi
  show (okArr (mkIx O) U)[j]? = some true
  have := okArr_iff (O := O) (U := U) (i := j)
  have h2 := this.2 (hS j hj)
  revert h2
  cases (okArr (mkIx O) U)[j]? <;> simp

end Elim

/-! ## Records -/

section Records

variable {U : Cand n m}

theorem pcB_le {κ : Key n m} {R : RoleT (Fin m)} {b : Fin n} : pcB κ R b ≤ 1 := by
  unfold pcB; split <;> omega

theorem pc_le (t : Ty n) (σ : Spec n m) (R : RoleT (Fin m)) (b : Fin n) :
    pcB (childKey (mkIx O) t σ) R b ≤ if cntP R b (flipL σ.lab, t) = true then 1 else 0 := by
  unfold pcB cntP childKey
  simp only [Finset.mem_inter, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem pc_eq_upper (t : Ty n) (σ : Spec n m) {u : Fin n × Nat × RoleT (Fin m) × Fin n}
    (hu : u ∈ upperL O) :
    pcB (childKey (mkIx O) t σ) u.2.2.1 u.2.2.2 =
      if cntP u.2.2.1 u.2.2.2 (flipL σ.lab, t) = true then 1 else 0 := by
  have hrel : u.2.2.1 ∈ flipL σ.lab → u.2.2.2 ∈ relI (mkIx O) (flipL σ.lab) :=
    fun hS => mem_relI_upper hu hS
  unfold pcB cntP childKey
  simp only [Finset.mem_inter, decide_eq_true_eq]
  split_ifs <;> simp_all

theorem cnt_eq (N : List (Nbr (Fin n) (Fin m))) (R : RoleT (Fin m)) (b : Fin n) :
    cnt N R b = N.countP (cntP R b) := rfl

/-- The edge to a child entry. -/
theorem cand_edge {A : Nat → Prop} (hA : ∀ j, A j → nodeOK (mkIx O) U j) {i : Nat}
    {c : Lab m × Ty n} (h : CandP O U A i c) : UpClosed O c.1 ∧ EdgeOK O (nd U i).ty c := by
  obtain ⟨e, -, ⟨-, hkey, hup⟩, j, hj, hAj, hb, rfl⟩ := h
  obtain ⟨-, hctx⟩ := mem_memb hj
  have hseed := (hA j hAj).2.2.2
  rw [hctx, hkey] at hseed
  refine ⟨upClosedB_sound hup, fun a S c hcl => ⟨fun hS ha => ?_, fun hS ha => ?_⟩⟩
  · exact hseed (Finset.mem_union_right _ (mem_fwdI.2 ⟨a, ha, S, hS, hcl⟩))
  · refine hb (mem_fwdI.2 ⟨a, ha, S, ?_, hcl⟩)
    rw [hctx, hkey]
    exact mem_flipL.2 hS

/-- The edge from the child of an entry back to the node. -/
theorem cand_par_edge {A : Nat → Prop} (hA : ∀ j, A j → nodeOK (mkIx O) U j) {i : Nat}
    {e : Entry n m} (hok : entryOK (mkIx O) U (nd U i).ty e) {j : Nat} (hj : j ∈ memb U e.kid)
    (hAj : A j) (hb : backOf (mkIx O) U j ⊆ (nd U i).ty) :
    UpClosed O (flipL e.spec.lab) ∧ EdgeOK O (nd U j).ty (flipL e.spec.lab, (nd U i).ty) := by
  obtain ⟨-, hkey, hup⟩ := hok
  obtain ⟨-, hctx⟩ := mem_memb hj
  have hseed := (hA j hAj).2.2.2
  rw [hctx, hkey] at hseed
  refine ⟨upClosed_flipL (upClosedB_sound hup), fun a S c hcl => ⟨fun hS ha => ?_, fun hS ha => ?_⟩⟩
  · refine hb (mem_fwdI.2 ⟨a, ha, S, ?_, hcl⟩)
    rw [hctx, hkey]
    exact hS
  · refine hseed (Finset.mem_union_right _ (mem_fwdI.2 ⟨a, ha, S, ?_, hcl⟩))
    simpa [mem_flipL] using hS

variable (O U) in
/-- The records of the live nodes. -/
def recs : Set (Rec (Fin n) (Fin m)) :=
  {ρ | (∃ i, Al O U i ∧ (keyOf U (nd U i).ctx).lab = ∅ ∧ ρ = ((nd U i).ty, none)) ∨
    ∃ i, Al O U i ∧ ∃ c, CandP O U (Al O U) i c ∧ ρ = childRec (nd U i).ty c}

/-- **The live nodes give a self-supporting set of records.** -/
theorem recs_selfSupp : SelfSupp O (recs O U) := by
  have hA : ∀ j, Al O U j → nodeOK (mkIx O) U j := fun j h => al_nodeOK h
  rintro ρ (⟨i, hi, hlab, rfl⟩ | ⟨i, hi, c, hc, rfl⟩)
  · obtain ⟨hok, -, E, hE, hlow, hupp⟩ := al_supp hi
    refine ⟨E, ?_, fun c hc => Or.inr ⟨i, hi, c, hE c hc, rfl⟩⟩
    rw [Proc.starOK_iff]
    have hpc : ∀ R b, pcB (keyOf U (nd U i).ctx) R b = 0 := fun R b => by simp [pcB, hlab]
    refine ⟨closedI_sound hok.2.2.1, fun c hc => cand_edge hA (hE c hc), fun q hq hqa => ?_,
      fun u hu hua => ?_⟩
    · have := hlow q (mem_lowAt.2 ⟨hq, hqa⟩)
      rw [hpc] at this
      simpa [cnt_eq] using this
    · have := hupp u (mem_uppAt.2 ⟨hu, hua⟩)
      rw [hpc] at this
      simpa [cnt_eq] using this
  · obtain ⟨e, he, hok, j, hj, hAj, hb, rfl⟩ := hc
    obtain ⟨hokj, -, E, hE, hlow, hupp⟩ := al_supp hAj
    refine ⟨E, ?_, fun c hc => Or.inr ⟨j, hAj, c, hE c hc, rfl⟩⟩
    have hctx := (mem_memb hj).2
    have hkey := hok.2.1
    simp only [childRec]
    rw [Proc.starOK_iff]
    refine ⟨closedI_sound hokj.2.2.1, fun c hc => ?_, fun q hq hqa => ?_, fun u hu hua => ?_⟩
    · rcases List.mem_append.1 hc with hc | hc
      · simp only [Option.toList_some, List.mem_singleton] at hc
        subst hc
        exact cand_par_edge hA hok hj hAj hb
      · exact cand_edge hA (hE c hc)
    · have h1 := hlow q (mem_lowAt.2 ⟨hq, hqa⟩)
      rw [hctx, hkey] at h1
      have h2 := pc_le (O := O) (nd U i).ty e.spec q.2.2.1 q.2.2.2
      rw [Option.toList_some, cnt_eq, List.singleton_append, List.countP_cons]
      omega
    · have h1 := hupp u (mem_uppAt.2 ⟨hu, hua⟩)
      rw [hctx, hkey] at h1
      have h2 := pc_eq_upper (O := O) (nd U i).ty e.spec hu
      rw [Option.toList_some, cnt_eq, List.singleton_append, List.countP_cons]
      omega

theorem al_good {i : Nat} (hi : Al O U i) (hlab : (keyOf U (nd U i).ctx).lab = ∅) :
    Good O ((nd U i).ty, none) :=
  ⟨recs O U, Or.inl ⟨i, hi, hlab, rfl⟩, recs_selfSupp⟩

end Records

/-! ## Readout -/

section Readout

variable {U : Cand n m}

theorem mem_foldl_inter {b : Fin n} : ∀ (ts : List (Ty n)) (t : Ty n),
    b ∈ ts.foldl (· ∩ ·) t ↔ b ∈ t ∧ ∀ t' ∈ ts, b ∈ t'
  | [], t => by simp
  | t' :: ts, t => by
    rw [List.foldl_cons, mem_foldl_inter ts]
    simp only [Finset.mem_inter, List.mem_cons, forall_eq_or_imp]
    tauto

theorem mem_rootTys {A : Array Bool} {k : Nat} {t : Ty n} :
    t ∈ rootTys U A k ↔ (keyOf U k).lab = ∅ ∧ ∃ i ∈ memb U k, A[i]?.getD false = true ∧
      t = (nd U i).ty := by
  unfold rootTys
  split
  · next h =>
    simp only [h, true_and, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨i, ⟨hi, hA⟩, rfl⟩
      exact ⟨i, hi, hA, rfl⟩
    · rintro ⟨i, hi, hA, rfl⟩
      exact ⟨i, ⟨hi, hA⟩, rfl⟩
  · next h => simp [h]

/-- The live root nodes of context `k` that hold `a`. -/
def RootWith (O : Ontology (Fin n) (Fin m)) (U : Cand n m) (k : Nat) (a : Fin n) (i : Nat) : Prop :=
  i ∈ memb U k ∧ Al O U i ∧ (keyOf U k).lab = ∅ ∧ a ∈ (nd U i).ty

theorem rowOf_none {k : Nat} {a : Fin n} :
    rowOf U (aliveArr (mkIx O) U) k a = none ↔ ∀ i, ¬ RootWith O U k a i := by
  unfold rowOf RootWith Al
  split
  · next h =>
    simp only [true_iff]
    rintro i ⟨hi, hal, hlab, ha⟩
    have : (nd U i).ty ∈ (rootTys U (aliveArr (mkIx O) U) k).filter fun t => decide (a ∈ t) := by
      refine List.mem_filter.2 ⟨mem_rootTys.2 ⟨hlab, i, hi, by simp [hal], rfl⟩, by simp [ha]⟩
    rw [h] at this
    simp at this
  · next t ts h =>
    simp only [reduceCtorEq, false_iff, not_forall, not_not]
    have ht : t ∈ (rootTys U (aliveArr (mkIx O) U) k).filter fun t => decide (a ∈ t) := by
      rw [h]; exact List.mem_cons_self
    obtain ⟨ht1, ht2⟩ := List.mem_filter.1 ht
    obtain ⟨hlab, i, hi, hal, rfl⟩ := mem_rootTys.1 ht1
    refine ⟨i, hi, ?_, hlab, by simpa using ht2⟩
    revert hal; cases (aliveArr (mkIx O) U)[i]? <;> simp

theorem rowOf_some {k : Nat} {a : Fin n} {L : List (Fin n)}
    (h : rowOf U (aliveArr (mkIx O) U) k a = some L) :
    (∃ i, RootWith O U k a i) ∧ ∀ b, b ∈ L ↔ ∀ i, RootWith O U k a i → b ∈ (nd U i).ty := by
  have hne : rowOf U (aliveArr (mkIx O) U) k a ≠ none := by rw [h]; simp
  have hex : ∃ i, RootWith O U k a i := by
    by_contra hc
    push Not at hc
    exact hne (rowOf_none.2 hc)
  refine ⟨hex, fun b => ?_⟩
  unfold rowOf at h
  split at h
  · simp at h
  · next t ts hl =>
    simp only [Option.some.injEq] at h
    subst h
    rw [Finset.mem_sort, mem_foldl_inter]
    have key : ∀ t', t' ∈ t :: ts ↔ ∃ i, RootWith O U k a i ∧ t' = (nd U i).ty := by
      intro t'
      rw [← hl, List.mem_filter, mem_rootTys]
      constructor
      · rintro ⟨⟨hlab, i, hi, hal, rfl⟩, ha⟩
        refine ⟨i, ⟨hi, ?_, hlab, by simpa using ha⟩, rfl⟩
        revert hal; unfold Al; cases (aliveArr (mkIx O) U)[i]? <;> simp
      · rintro ⟨i, ⟨hi, hal, hlab, ha⟩, rfl⟩
        exact ⟨⟨hlab, i, hi, by unfold Al at hal; simp [hal], rfl⟩, by simpa using ha⟩
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases List.mem_cons.1 ((key _).2 ⟨i, hi, rfl⟩) with he | he
      · rw [he]; exact h1
      · exact h2 _ he
    · intro hall
      refine ⟨?_, fun t' ht' => ?_⟩
      · obtain ⟨i, hi, he⟩ := (key t).1 List.mem_cons_self
        rw [he]; exact hall i hi
      · obtain ⟨i, hi, he⟩ := (key t').1 (List.mem_cons_of_mem _ ht')
        rw [he]; exact hall i hi

theorem rootWith_good {k : Nat} {a : Fin n} {i : Nat} (h : RootWith O U k a i) :
    Good O ((nd U i).ty, none) := by
  obtain ⟨hi, hal, hlab, -⟩ := h
  refine al_good hal ?_
  rw [(mem_memb hi).2]
  exact hlab

/-- **Soundness, for every candidate set.** A listed row belongs to a
requested name, the name is satisfiable, and the row contains every
subsumer. -/
theorem fastRows_sound (hA : IsALCHIQ O) {req : List (Fin n)}
    {p : Fin n × Option (List (Fin n))} (hp : p ∈ fastRows (mkIx O) U req) :
    p.1 ∈ req ∧ ∀ L, p.2 = some L →
      (∀ b, EntailsSub O p.1 b → b ∈ L) ∧
      ¬ (∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) := by
  simp only [fastRows, List.mem_map] at hp
  obtain ⟨⟨a, k⟩, hak, rfl⟩ := hp
  refine ⟨(List.of_mem_zip hak).1, fun L hL => ?_⟩
  obtain ⟨⟨i, hi⟩, hL'⟩ := rowOf_some hL
  refine ⟨fun b hb => (hL' b).2 fun j hj => ?_, fun hun => ?_⟩
  · exact (entailsSub_iff_star O hA a b).1 hb _ (rootWith_good hj) hj.2.2.2
  · exact (unsat_iff_no_star O hA a).1 hun _ (rootWith_good hi) hi.2.2.2

end Readout

end ContextCalculus.SRIQ.Fast

#print axioms ContextCalculus.SRIQ.Fast.suppB_iff
#print axioms ContextCalculus.SRIQ.Fast.subset_al
#print axioms ContextCalculus.SRIQ.Fast.recs_selfSupp
#print axioms ContextCalculus.SRIQ.Fast.fastRows_sound
