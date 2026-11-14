import ContextCalculus.SRIQ.FastSound

/-!
# Certificate check for the fast SHIQ procedure: completeness (stage C1c)

If `U` passes the closure check (`ClosedP`), every model element of a
requested name has a live root node below its type (`complete`).

Fix a model `I`. A node *simulates* an element `z` with optional parent
`py` (`Sim`) when its type lies below the type of `z` and its parent label
and projection lie below the label to `py` and the type of `py`. A
simulating node is *type-maximal* (`TypeMax`) when no simulating node of
the same context has a strictly larger type. The closure conditions only
ever ask for nodes with larger types in the node's own context (R4, and
R6 when the fillers are missing) or for specs in the node's own pool (R3,
R5, R6), so at a type-maximal node every condition instantiated by the
model is already met (`no_variant`).

The set `SS` of type-maximal nodes that also meet the parent-witness
condition `PG` supports itself (`ss_supp`), so it is live (`subset_al`).
For a node of `SS` the star is built from a *configuration*: a finite set
of pairs (model neighbour, pool entry) whose specs are maximal among the
valid specs of the pool, covering every demand copy (`Cover`), of least
size. Least size gives the upper bounds: two entries for one neighbour
that both count for an at-most clause would merge (R5), and an entry for
the parent element that counts together with the parent entry would drop
(`PG`). The children are type-maximal nodes of the entries' contexts; they
meet `PG` because the entry's spec is maximal and R6 holds at the node
(`child_pg`), and their back sets lie in the node's type by R4
(`back_sub`).
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat} {O : Ontology (Fin n) (Fin m)} {U : Cand n m} {req : List (Fin n)}
variable {D : Type} {I : Interp D (Fin n) (Fin m)}

/-! ## Model facts -/

section Model

theorem closed_typeOf (hI : models I O) (x : D) : Closed O (typeOf I x) := by
  rw [closed_iff]
  intro body head hcl hbody
  obtain ⟨b, hb, hbx⟩ := hI _ hcl x fun a ha => (mem_typeOf I).1 (hbody a ha)
  exact ⟨b, hb, (mem_typeOf I).2 hbx⟩

theorem fwdI_model (hI : models I O) {t : Ty n} {L : Lab m} {z w : D} (ht : t ⊆ typeOf I z)
    (hL : L ⊆ labelOf I z w) : fwdI (mkIx O) t L ⊆ typeOf I w := by
  intro c hc
  obtain ⟨a, ha, S, hS, hcl⟩ := mem_fwdI.1 hc
  exact (mem_typeOf I).2 (hI _ hcl z ((mem_typeOf I).1 (ht ha)) w ((mem_labelOf I).1 (hL hS)))

theorem flipL_mono {L L' : Lab m} (h : L ⊆ L') : flipL L ⊆ flipL L' := by
  intro S hS
  rw [mem_flipL] at hS ⊢
  exact h hS

theorem flipL_sub_label {L : Lab m} {z w : D} (h : L ⊆ labelOf I z w) :
    flipL L ⊆ labelOf I w z := by
  rw [← flipL_labelOf]
  exact flipL_mono h

theorem upS_sub_label (hI : models I O) {R : RoleT (Fin m)} {z w : D} (h : I.rt R z w) :
    upS (mkIx O) R ⊆ labelOf I z w := fun S hS =>
  (mem_labelOf I).2 (roleLe_sound hI (upS_sound hS) z w h)

/-- The witnesses of a lower clause at a model element. -/
theorem lower_wit (hI : models I O) {q : Fin n × Nat × RoleT (Fin m) × Fin n} (hq : q ∈ lowerL O)
    {z : D} (ha : I.c q.1 z) :
    ∃ l : List D, l.Nodup ∧ l.length = q.2.1 ∧ ∀ w ∈ l, I.rt q.2.2.1 z w ∧ I.c q.2.2.2 w := by
  rcases mem_lowerL.1 hq with ⟨hk, hcl⟩ | hcl
  · obtain ⟨w, hw1, hw2⟩ := hI _ hcl z ha
    refine ⟨[w], List.nodup_singleton w, by simp [hk], fun w' hw' => ?_⟩
    rw [List.mem_singleton.1 hw']
    exact ⟨hw1, hw2⟩
  · exact hI _ hcl z ha

/-- An at-most clause bounds any duplicate-free list of successors. -/
theorem upper_bound (hI : models I O) {u : Fin n × Nat × RoleT (Fin m) × Fin n} (hu : u ∈ upperL O)
    {z : D} (ha : I.c u.1 z) {l : List D} (hl : l.Nodup)
    (hs : ∀ w ∈ l, I.rt u.2.2.1 z w ∧ I.c u.2.2.2 w) : l.length ≤ u.2.1 :=
  hI _ (mem_upperL.1 hu) z ha l hl hs

end Model

/-! ## Simulation -/

section Sim

variable (U I)

/-- Node `i` simulates `z` with parent `py`. -/
def Sim (i : Nat) (z : D) (py : Option D) : Prop :=
  (nd U i).ty ⊆ typeOf I z ∧ match py with
    | none => (keyOf U (nd U i).ctx).lab = ∅
    | some y => (keyOf U (nd U i).ctx).lab ⊆ labelOf I z y ∧ (keyOf U (nd U i).ctx).pi ⊆ typeOf I y

/-- No simulating node of the same context has a strictly larger type. -/
def TypeMax (i : Nat) (z : D) (py : Option D) : Prop :=
  i ∈ memb U (nd U i).ctx ∧ Sim U I i z py ∧
    ∀ j ∈ memb U (nd U i).ctx, Sim U I j z py → (nd U i).ty ⊆ (nd U j).ty → (nd U j).ty ⊆ (nd U i).ty

/-- A spec is valid for the model pair `z, w`. -/
def Valid (z w : D) (σ : Spec n m) : Prop := σ.lab ⊆ labelOf I z w ∧ σ.fill ⊆ typeOf I w

/-- A valid spec with no larger valid spec in the pool of `i`. -/
def MaxValid (i : Nat) (z w : D) (σ : Spec n m) : Prop :=
  Valid I z w σ ∧ ∀ e ∈ (nd U i).pool, Valid I z w e.spec → σ.le e.spec → e.spec.le σ

variable (O)

/-- The parent-witness condition: a spec that may count for an upper clause
counted by the parent entry, and that is valid for the parent element,
serves only demands the parent entry meets. -/
def PG (i : Nat) (z : D) (py : Option D) : Prop :=
  ∀ y, py = some y → ∀ u ∈ uppAt (mkIx O) (nd U i).ty,
    pcB (keyOf U (nd U i).ctx) u.2.2.1 u.2.2.2 = 1 → u.2.1 < pot (mkIx O) U i u.2.2.1 u.2.2.2 →
    ∀ σ ∈ cset U i u.2.2.1 u.2.2.2, Valid I z y σ.spec →
      σ.spec.lab ⊆ (keyOf U (nd U i).ctx).lab ∧
      σ.spec.fill ∩ relI (mkIx O) (keyOf U (nd U i).ctx).lab ⊆ (keyOf U (nd U i).ctx).pi

/-- The nodes that the completeness proof keeps. -/
def SS (i : Nat) : Prop := ∃ z py, TypeMax U I i z py ∧ PG O U I i z py

variable {O U I}

theorem sim_of_ctx {i j : Nat} {z : D} {py : Option D} (hc : (nd U j).ctx = (nd U i).ctx)
    (hs : Sim U I i z py) (ht : (nd U j).ty ⊆ typeOf I z) : Sim U I j z py := by
  refine ⟨ht, ?_⟩
  rw [hc]
  exact hs.2

theorem nodeClosed (hC : ClosedP (mkIx O) U req) {i k : Nat} (hi : i ∈ memb U k) :
    NodeClosed (mkIx O) U i :=
  hC.2.2.2 i (mem_memb hi).1

/-- Every set of `br s` contains a node of `k`; one below a closed model type. -/
theorem cover_real (hI : models I O) {k : Nat} {s : Ty n} (hb : BranchCov (mkIx O) U k s) {w : D}
    (hs : s ⊆ typeOf I w) : ∃ j ∈ memb U k, s ⊆ (nd U j).ty ∧ (nd U j).ty ⊆ typeOf I w := by
  obtain ⟨b, hb', hbT⟩ := br_guided (closed_typeOf hI w) hs
  obtain ⟨j, hj, h1, h2⟩ := hb b hb'
  exact ⟨j, hj, h1, h2.trans hbT⟩

/-- A simulating node of a context gives a type-maximal one. -/
theorem typeMax_exists {k j : Nat} {w : D} {py : Option D} (hj : j ∈ memb U k)
    (hs : Sim U I j w py) : ∃ j', (nd U j').ctx = k ∧ TypeMax U I j' w py := by
  classical
  let Q := ((memb U k).filter fun j => decide (Sim U I j w py)).toFinset
  have hQ : Q.Nonempty := ⟨j, List.mem_toFinset.2 (List.mem_filter.2 ⟨hj, by simpa using hs⟩)⟩
  obtain ⟨j', hj', hmax⟩ := Finset.exists_max_image Q (fun j => (nd U j).ty.card) hQ
  obtain ⟨hj'm, hj's⟩ := List.mem_filter.1 (List.mem_toFinset.1 hj')
  have hctx := (mem_memb hj'm).2
  refine ⟨j', hctx, ?_, of_decide_eq_true hj's, fun j'' hj'' hs'' hsub => ?_⟩
  · rw [hctx]; exact hj'm
  · rw [hctx] at hj''
    have := hmax j'' (List.mem_toFinset.2 (List.mem_filter.2 ⟨hj'', by simpa using hs''⟩))
    exact (Finset.eq_of_subset_of_card_le hsub this).symm.subset

/-- **No variant.** At a type-maximal node, a covered seed `t ∪ X` with `X`
below the model type adds nothing. -/
theorem no_variant (hI : models I O) {i : Nat} {z : D} {py : Option D} (hm : TypeMax U I i z py)
    {X : Ty n} (hb : BranchCov (mkIx O) U (nd U i).ctx ((nd U i).ty ∪ X)) (hX : X ⊆ typeOf I z) :
    X ⊆ (nd U i).ty := by
  obtain ⟨j, hj, h1, h2⟩ := cover_real hI hb (Finset.union_subset hm.2.1.1 hX)
  have hs : Sim U I j z py := sim_of_ctx (mem_memb hj).2 hm.2.1 h2
  have := hm.2.2 j hj hs (Finset.subset_union_left.trans h1)
  exact (Finset.subset_union_right.trans h1).trans this

theorem key_kid {i : Nat} {e : Entry n m} (hok : entryOK (mkIx O) U (nd U i).ty e) {j : Nat}
    (hj : j ∈ memb U e.kid) : keyOf U (nd U j).ctx = childKey (mkIx O) (nd U i).ty e.spec := by
  rw [(mem_memb hj).2]; exact hok.2.1

/-- A valid entry has a type-maximal simulating child. -/
theorem child_exists (hI : models I O) (hC : ClosedP (mkIx O) U req) {i : Nat} {z w : D}
    {py : Option D} (hs : Sim U I i z py) {e : Entry n m} (hok : entryOK (mkIx O) U (nd U i).ty e)
    (hv : Valid I z w e.spec) : ∃ j, (nd U j).ctx = e.kid ∧ TypeMax U I j w (some z) := by
  have hseed : (keyOf U e.kid).seed ⊆ typeOf I w := by
    rw [hok.2.1]
    exact Finset.union_subset hv.2 (fwdI_model hI hs.1 hv.1)
  obtain ⟨j, hj, h1, h2⟩ := cover_real hI (hC.2.2.1 e.kid hok.1) hseed
  have hsj : Sim U I j w (some z) := by
    refine ⟨h2, ?_, ?_⟩
    · rw [key_kid hok hj]; exact flipL_sub_label hv.1
    · rw [key_kid hok hj]; exact Finset.inter_subset_left.trans hs.1
  exact typeMax_exists hj hsj

/-- The back set of a simulating node lies below the parent element. -/
theorem back_model (hI : models I O) {j : Nat} {w z : D} (hs : Sim U I j w (some z)) :
    backOf (mkIx O) U j ⊆ typeOf I z :=
  fwdI_model hI hs.1 hs.2.1

theorem valid_union {z w : D} {σ τ : Spec n m} (h1 : Valid I z w σ) (h2 : Valid I z w τ) :
    Valid I z w (σ.union τ) :=
  ⟨Finset.union_subset h1.1 h2.1, Finset.union_subset h1.2 h2.2⟩

theorem le_union_left (σ τ : Spec n m) : σ.le (σ.union τ) :=
  ⟨Finset.subset_union_left, Finset.subset_union_left⟩

theorem le_union_right (σ τ : Spec n m) : τ.le (σ.union τ) :=
  ⟨Finset.subset_union_right, Finset.subset_union_right⟩

/-- A valid pool entry lies below a maximal valid one. -/
theorem maxValid_above {i : Nat} {z w : D} {e : Entry n m} (he : e ∈ (nd U i).pool)
    (hv : Valid I z w e.spec) :
    ∃ e' ∈ (nd U i).pool, e.spec.le e'.spec ∧ MaxValid U I i z w e'.spec := by
  classical
  let Q := ((nd U i).pool.filter fun e' => decide (Valid I z w e'.spec ∧ e.spec.le e'.spec)).toFinset
  have hQ : Q.Nonempty :=
    ⟨e, List.mem_toFinset.2 (List.mem_filter.2 ⟨he, by simpa using ⟨hv, Finset.Subset.refl _,
      Finset.Subset.refl _⟩⟩)⟩
  obtain ⟨e', he', hmax⟩ := Finset.exists_max_image Q
    (fun e' => e'.spec.lab.card + e'.spec.fill.card) hQ
  obtain ⟨he'p, he'v⟩ := List.mem_filter.1 (List.mem_toFinset.1 he')
  have he'v' := of_decide_eq_true he'v
  refine ⟨e', he'p, he'v'.2, he'v'.1, fun e'' he'' hv'' hle => ?_⟩
  have := hmax e'' (List.mem_toFinset.2 (List.mem_filter.2 ⟨he'', by
    simpa using ⟨hv'', he'v'.2.1.trans hle.1, he'v'.2.2.trans hle.2⟩⟩))
  have h1 := Finset.card_le_card hle.1
  have h2 := Finset.card_le_card hle.2
  exact ⟨(Finset.eq_of_subset_of_card_le hle.1 (by omega)).symm.subset,
    (Finset.eq_of_subset_of_card_le hle.2 (by omega)).symm.subset⟩

/-- **The child condition.** The type-maximal child of a maximal valid entry
of a type-maximal node meets `PG` (R6). -/
theorem child_pg (hI : models I O) (hC : ClosedP (mkIx O) U req) {i : Nat} {z w : D}
    {py : Option D} (hm : TypeMax U I i z py) {e : Entry n m} (he : e ∈ (nd U i).pool)
    (hmv : MaxValid U I i z w e.spec) {j : Nat} (hjc : (nd U j).ctx = e.kid)
    (hmj : TypeMax U I j w (some z)) : PG O U I j w (some z) := by
  have hNC := nodeClosed hC hm.1
  have hok := hNC.2.1 e he
  have hjm : j ∈ memb U e.kid := hjc ▸ hmj.1
  intro y hy u hu hpc hpot σ hσ hv
  simp only [Option.some.injEq] at hy
  subst hy
  have hkey := key_kid hok hjm
  have hW := hNC.2.2.2.2.2 e he j hjm u hu (by rw [← hjc]; exact hpc) hpot σ hσ
  have hfill : σ.spec.fill ⊆ (nd U i).ty := by
    by_contra hn
    exact hn (no_variant hI hm (hW.2 hn) hv.2)
  obtain ⟨e', he', hspec⟩ := hW.1 hfill
  have hvg : Valid I z w e'.spec := by
    rw [hspec]
    refine ⟨Finset.union_subset hmv.1.1 ?_, hmv.1.2⟩
    rw [← flipL_labelOf]
    exact flipL_mono hv.1
  have hle : e.spec.le e'.spec := by
    rw [hspec]; exact ⟨Finset.subset_union_left, Finset.Subset.refl _⟩
  have hback := hmv.2 e' he' hvg hle
  rw [hspec] at hback
  rw [hkey]
  simp only [childKey]
  refine ⟨fun S hS => ?_, ?_⟩
  · rw [mem_flipL]
    exact hback.1 (Finset.mem_union_right _ (mem_flipL.2 (by simpa using hS)))
  · intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_inter.1 hb
    exact Finset.mem_inter.2 ⟨hfill hb1, hb2⟩

end Sim

end ContextCalculus.SRIQ.Fast
