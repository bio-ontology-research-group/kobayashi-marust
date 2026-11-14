import ContextCalculus.SRIQ.FastSound
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-! ## Configurations -/

section Config

open Classical

variable (O U I)

/-- A spec serves a lower clause: it has the role and the filler. -/
def Covers (q : Fin n × Nat × RoleT (Fin m) × Fin n) (σ : Spec n m) : Prop :=
  q.2.2.1 ∈ σ.lab ∧ q.2.2.2 ∈ σ.fill

/-- The model elements that serve `q` in configuration `E`, with the parent
element when the parent entry counts for `q`. -/
noncomputable def coverSet (i : Nat) (py : Option D) (E : Finset (D × Entry n m))
    (q : Fin n × Nat × RoleT (Fin m) × Fin n) : Finset D :=
  (E.filter fun p => Covers q p.2.spec).image Prod.fst ∪
    (if pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2 = 1 then py.toFinset else ∅)

/-- Every pair of the configuration is a pool entry with a maximal valid spec. -/
def CfgOK (i : Nat) (z : D) (E : Finset (D × Entry n m)) : Prop :=
  ∀ p ∈ E, p.2 ∈ (nd U i).pool ∧ MaxValid U I i z p.1 p.2.spec

/-- Every lower clause at the node has as many serving elements as its number. -/
def Cover (i : Nat) (py : Option D) (E : Finset (D × Entry n m)) : Prop :=
  ∀ q ∈ lowAt (mkIx O) (nd U i).ty, q.2.1 ≤ (coverSet U i py E q).card

variable {O U I}

theorem coverSet_mono {i : Nat} {py : Option D} {E E' : Finset (D × Entry n m)} (h : E ⊆ E')
    (q : Fin n × Nat × RoleT (Fin m) × Fin n) : coverSet U i py E q ⊆ coverSet U i py E' q := by
  unfold coverSet
  refine Finset.union_subset_union (Finset.image_subset_image ?_) (Finset.Subset.refl _)
  exact Finset.filter_subset_filter _ h

theorem coverSet_erase {i : Nat} {py : Option D} {E : Finset (D × Entry n m)} (p : D × Entry n m)
    (q : Fin n × Nat × RoleT (Fin m) × Fin n) :
    coverSet U i py E q ⊆ insert p.1 (coverSet U i py (E.erase p) q) := by
  intro x hx
  unfold coverSet at hx ⊢
  rcases Finset.mem_union.1 hx with hx | hx
  · obtain ⟨p', hp', rfl⟩ := Finset.mem_image.1 hx
    by_cases he : p' = p
    · subst he; exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.2 ⟨p', ?_, rfl⟩))
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp'
      exact Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨he, h1⟩, h2⟩
  · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)

theorem covers_le {q : Fin n × Nat × RoleT (Fin m) × Fin n} {σ τ : Spec n m} (h : Covers q σ)
    (hle : σ.le τ) : Covers q τ := ⟨hle.1 h.1, hle.2 h.2⟩

theorem upAux_mono (R : RoleT (Fin m)) : ∀ (f : Nat) (acc : Lab m) (q : List (RoleT (Fin m))),
    acc ⊆ upAux (mkIx O).stepsBy f acc q
  | 0, acc, q => by simp [upAux]
  | _ + 1, acc, [] => by simp [upAux]
  | f + 1, acc, x :: rest => by
    simp only [upAux]
    exact Finset.subset_union_left.trans (upAux_mono R f _ _)

theorem upS_self (R : RoleT (Fin m)) : R ∈ upS (mkIx O) R := by
  simp only [upS, mkIx, Array.getElem?_ofFn, rc_lt R, dite_true, Option.getD_some]
  rw [ofRc_rc]
  exact upAux_mono (O := O) R _ _ _ (Finset.mem_singleton_self R)

theorem dflt_covers (q : Fin n × Nat × RoleT (Fin m) × Fin n) : Covers q (dflt (mkIx O) q) :=
  ⟨upS_self q.2.2.1, Finset.mem_singleton_self _⟩

theorem pc_some {i : Nat} {z : D} {py : Option D} (hs : Sim U I i z py) {R : RoleT (Fin m)}
    {b : Fin n} (h : pcB (keyOf U (nd U i).ctx) R b = 1) :
    ∃ y, py = some y ∧ I.rt R z y ∧ I.c b y := by
  unfold pcB at h
  split at h
  · next hh =>
    obtain ⟨hs1, hs2⟩ := hs
    cases py with
    | none => simp_all
    | some y =>
      exact ⟨y, rfl, (mem_labelOf I).1 (hs2.1 hh.1), (mem_typeOf I).1 (hs2.2 hh.2)⟩
  · simp at h

theorem pcB_cases (κ : Key n m) (R : RoleT (Fin m)) (b : Fin n) : pcB κ R b = 0 ∨ pcB κ R b = 1 := by
  unfold pcB; split <;> simp

/-- Entries for every listed witness of a lower clause. -/
theorem cfg_wit (hI : models I O) {i : Nat} {z : D} {q : Fin n × Nat × RoleT (Fin m) × Fin n}
    (hd : inPool U i (dflt (mkIx O) q)) :
    ∀ l : List D, (∀ w ∈ l, I.rt q.2.2.1 z w ∧ I.c q.2.2.2 w) →
      ∃ F, CfgOK U I i z F ∧ ∀ w ∈ l, ∃ p ∈ F, p.1 = w ∧ Covers q p.2.spec
  | [], _ => ⟨∅, by simp [CfgOK], by simp⟩
  | w :: l, hl => by
    obtain ⟨F, hF, hFl⟩ := cfg_wit hI hd l fun w' h => hl w' (List.mem_cons_of_mem _ h)
    obtain ⟨e, he, hspec⟩ := hd
    have hw := hl w List.mem_cons_self
    have hv : Valid I z w e.spec := by
      rw [hspec]
      exact ⟨upS_sub_label hI hw.1, by simpa [dflt] using (mem_typeOf I).2 hw.2⟩
    obtain ⟨e', he', hle, hmv⟩ := maxValid_above he hv
    refine ⟨insert (w, e') F, fun p hp => ?_, fun w' hw' => ?_⟩
    · rcases Finset.mem_insert.1 hp with rfl | hp
      · exact ⟨he', hmv⟩
      · exact hF p hp
    · rcases List.mem_cons.1 hw' with rfl | hw'
      · exact ⟨(w', e'), Finset.mem_insert_self _ _, rfl,
          covers_le (by rw [hspec]; exact dflt_covers q) hle⟩
      · obtain ⟨p, hp, h1, h2⟩ := hFl w' hw'
        exact ⟨p, Finset.mem_insert_of_mem hp, h1, h2⟩

/-- A configuration exists. -/
theorem cfg_exists (hI : models I O) (hC : ClosedP (mkIx O) U req) {i : Nat} {z : D}
    {py : Option D} (hm : TypeMax U I i z py) : ∃ E, CfgOK U I i z E ∧ Cover O U i py E := by
  have hNC := nodeClosed hC hm.1
  suffices h : ∀ Q : List (Fin n × Nat × RoleT (Fin m) × Fin n),
      (∀ q ∈ Q, q ∈ lowAt (mkIx O) (nd U i).ty) →
      ∃ E, CfgOK U I i z E ∧ ∀ q ∈ Q, q.2.1 ≤ (coverSet U i py E q).card from
    h _ fun q hq => hq
  intro Q
  induction Q with
  | nil => exact fun _ => ⟨∅, by simp [CfgOK], by simp⟩
  | cons q Q ih =>
    intro hQ
    obtain ⟨E, hE, hEQ⟩ := ih fun q' h => hQ q' (List.mem_cons_of_mem _ h)
    have hq := hQ q List.mem_cons_self
    have hmono : ∀ F, CfgOK U I i z F → CfgOK U I i z (E ∪ F) ∧
        ∀ q' ∈ Q, q'.2.1 ≤ (coverSet U i py (E ∪ F) q').card := fun F hF =>
      ⟨fun p hp => (Finset.mem_union.1 hp).elim (hE p) (hF p),
        fun q' hq' => (hEQ q' hq').trans (Finset.card_le_card
          (coverSet_mono Finset.subset_union_left q'))⟩
    by_cases hk : q.2.1 = 0
    · exact ⟨E, hE, fun q' hq' => by
        rcases List.mem_cons.1 hq' with rfl | hq'
        · omega
        · exact hEQ q' hq'⟩
    by_cases hsk : skipQ (keyOf U (nd U i).ctx) q
    · obtain ⟨y, rfl, -, -⟩ := pc_some hm.2.1 hsk.2
      refine ⟨E, hE, fun q' hq' => ?_⟩
      rcases List.mem_cons.1 hq' with rfl | hq'
      · rw [hsk.1]
        refine Finset.card_pos.2 ⟨y, Finset.mem_union_right _ ?_⟩
        simp [hsk.2]
      · exact hEQ q' hq'
    · have hd := hNC.2.2.1 q hq (by omega) hsk
      obtain ⟨hql, hqa⟩ := mem_lowAt.1 hq
      obtain ⟨l, hnd, hlen, hl⟩ := lower_wit hI hql ((mem_typeOf I).1 (hm.2.1.1 hqa))
      obtain ⟨F, hF, hFl⟩ := cfg_wit hI hd l hl
      obtain ⟨h1, h2⟩ := hmono F hF
      refine ⟨E ∪ F, h1, fun q' hq' => ?_⟩
      rcases List.mem_cons.1 hq' with rfl | hq'
      · rw [← hlen, ← List.toFinset_card_of_nodup hnd]
        refine Finset.card_le_card fun w hw => ?_
        obtain ⟨p, hp, rfl, hcov⟩ := hFl w (List.mem_toFinset.1 hw)
        exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨p, Finset.mem_filter.2
          ⟨Finset.mem_union_right _ hp, hcov⟩, rfl⟩)
      · exact h2 q' hq'

/-- A configuration of least size. -/
theorem cfg_min (hI : models I O) (hC : ClosedP (mkIx O) U req) {i : Nat} {z : D}
    {py : Option D} (hm : TypeMax U I i z py) :
    ∃ E, CfgOK U I i z E ∧ Cover O U i py E ∧
      ∀ E', CfgOK U I i z E' → Cover O U i py E' → E.card ≤ E'.card := by
  have hex : ∃ k, ∃ E, CfgOK U I i z E ∧ Cover O U i py E ∧ E.card = k := by
    obtain ⟨E, h1, h2⟩ := cfg_exists hI hC hm
    exact ⟨_, E, h1, h2, rfl⟩
  obtain ⟨E, h1, h2, h3⟩ := Nat.find_spec hex
  refine ⟨E, h1, h2, fun E' h1' h2' => ?_⟩
  rw [h3]
  exact Nat.find_min' hex ⟨E', h1', h2', rfl⟩

/-- Every pair of a least configuration is needed for some lower clause. -/
theorem crit_exists {i : Nat} {z : D} {py : Option D} {E : Finset (D × Entry n m)}
    (hE : CfgOK U I i z E) (hcv : Cover O U i py E) (hmin : ∀ E', CfgOK U I i z E' → Cover O U i py E' → E.card ≤ E'.card)
    {p : D × Entry n m} (hp : p ∈ E) :
    ∃ q ∈ lowAt (mkIx O) (nd U i).ty, Covers q p.2.spec ∧
      (coverSet U i py (E.erase p) q).card < q.2.1 ∧ p.1 ∉ coverSet U i py (E.erase p) q := by
  have hok : CfgOK U I i z (E.erase p) := fun p' hp' => hE p' (Finset.mem_of_mem_erase hp')
  have hnc : ¬ Cover O U i py (E.erase p) := fun hc =>
    absurd (hmin _ hok hc) (by have := Finset.card_erase_lt_of_mem hp; omega)
  simp only [Cover, not_forall, not_le] at hnc
  obtain ⟨q, hq, hlt⟩ := hnc
  have hcov : Covers q p.2.spec := by
    by_contra hn
    have : coverSet U i py E q ⊆ coverSet U i py (E.erase p) q := by
      intro x hx
      rcases Finset.mem_insert.1 (coverSet_erase p q hx) with rfl | hx
      · unfold coverSet at hx ⊢
        rcases Finset.mem_union.1 hx with hx | hx
        · obtain ⟨p', hp', he⟩ := Finset.mem_image.1 hx
          obtain ⟨hp'E, hp'c⟩ := Finset.mem_filter.1 hp'
          have hne : p' ≠ p := fun h => hn (h ▸ hp'c)
          exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨p', Finset.mem_filter.2
            ⟨Finset.mem_erase.2 ⟨hne, hp'E⟩, hp'c⟩, he⟩)
        · exact Finset.mem_union_right _ hx
      · exact hx
    have := Finset.card_le_card this
    have := hcv q hq
    omega
  refine ⟨q, hq, hcov, hlt, fun hin => ?_⟩
  have hsub : coverSet U i py E q ⊆ coverSet U i py (E.erase p) q := by
    intro x hx
    rcases Finset.mem_insert.1 (coverSet_erase p q hx) with rfl | hx
    · exact hin
    · exact hx
  have := Finset.card_le_card hsub
  have := hcv q hq
  omega

end Config

/-! ## The star of a node of `SS` -/

section Star

open Classical

variable (U I)

/-- The type-maximal child chosen for a configuration pair. -/
noncomputable def kidOf (z : D) (p : D × Entry n m) : Nat :=
  if h : ∃ j, (nd U j).ctx = p.2.kid ∧ TypeMax U I j p.1 (some z) then h.choose else 0

/-- The star entry of a configuration pair. -/
noncomputable def entOf (z : D) (p : D × Entry n m) : Lab m × Ty n :=
  (p.2.spec.lab, (nd U (kidOf U I z p)).ty)

variable {U I}

theorem sum_toFinset_le {α : Type} (l : List α) (f : α → Nat) :
    l.toFinset.sum f ≤ (l.map f).sum := by
  rw [Finset.sum_list_map_count]
  refine Finset.sum_le_sum fun x hx => ?_
  have : 1 ≤ l.count x := List.count_pos_iff.2 (List.mem_toFinset.1 hx)
  rw [Nat.nsmul_eq_mul]
  exact Nat.le_mul_of_pos_left _ this

theorem countP_toList {α β : Type} (E : Finset α) (f : α → β) (P : β → Bool) :
    (E.toList.map f).countP P = (E.filter fun a => P (f a) = true).card := by
  rw [List.countP_map]
  have := Multiset.coe_countP (fun a => P (f a) = true) E.toList
  simp only [Bool.decide_eq_true] at this
  show List.countP (fun b => P (f b)) E.toList = _
  rw [← this, Finset.coe_toList, Multiset.countP_eq_card_filter]
  rfl

/-- The fixed data of the star construction at node `i`. -/
structure StarData (O : Ontology (Fin n) (Fin m)) (U : Cand n m) (req : List (Fin n))
    (I : Interp D (Fin n) (Fin m)) (i : Nat) (z : D) (py : Option D)
    (E : Finset (D × Entry n m)) : Prop where
  hI : models I O
  hC : ClosedP (mkIx O) U req
  hm : TypeMax U I i z py
  hpg : PG O U I i z py
  hE : CfgOK U I i z E
  hcv : Cover O U i py E
  hmin : ∀ E', CfgOK U I i z E' → Cover O U i py E' → E.card ≤ E'.card

variable {i : Nat} {z : D} {py : Option D} {E : Finset (D × Entry n m)}

theorem StarData.nc (h : StarData O U req I i z py E) : NodeClosed (mkIx O) U i :=
  nodeClosed h.hC h.hm.1

theorem StarData.ok (h : StarData O U req I i z py E) {p : D × Entry n m} (hp : p ∈ E) :
    entryOK (mkIx O) U (nd U i).ty p.2 :=
  h.nc.2.1 p.2 (h.hE p hp).1

theorem StarData.kid (h : StarData O U req I i z py E) {p : D × Entry n m} (hp : p ∈ E) :
    (nd U (kidOf U I z p)).ctx = p.2.kid ∧ TypeMax U I (kidOf U I z p) p.1 (some z) := by
  have hex := child_exists h.hI h.hC h.hm.2.1 (h.ok hp) (h.hE p hp).2.1
  unfold kidOf
  rw [dif_pos hex]
  exact hex.choose_spec

theorem StarData.kid_memb (h : StarData O U req I i z py E) {p : D × Entry n m} (hp : p ∈ E) :
    kidOf U I z p ∈ memb U p.2.kid := by
  have := (h.kid hp).2.1
  rw [(h.kid hp).1] at this
  exact this

theorem StarData.fill_sub (h : StarData O U req I i z py E) {p : D × Entry n m} (hp : p ∈ E) :
    p.2.spec.fill ⊆ (nd U (kidOf U I z p)).ty := by
  have hNC := nodeClosed h.hC (h.kid_memb hp)
  have hseed := hNC.1.2.2.2
  rw [(h.kid hp).1, (h.ok hp).2.1] at hseed
  exact Finset.subset_union_left.trans hseed

theorem StarData.cnt_of_covers (h : StarData O U req I i z py E) {p : D × Entry n m} (hp : p ∈ E)
    {q : Fin n × Nat × RoleT (Fin m) × Fin n} (hc : Covers q p.2.spec) :
    cntP q.2.2.1 q.2.2.2 (entOf U I z p) = true := by
  simp only [cntP, entOf, decide_eq_true_eq]
  exact ⟨hc.1, h.fill_sub hp hc.2⟩

theorem card_py_le {py : Option D} : py.toFinset.card ≤ 1 := by
  cases py <;> simp

/-- **Lower bounds.** -/
theorem StarData.lower (h : StarData O U req I i z py E) {q : Fin n × Nat × RoleT (Fin m) × Fin n}
    (hq : q ∈ lowAt (mkIx O) (nd U i).ty) :
    q.2.1 ≤ pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2 +
      (E.toList.map (entOf U I z)).countP (cntP q.2.2.1 q.2.2.2) := by
  rw [countP_toList]
  have h1 := h.hcv q hq
  have h2 : (coverSet U i py E q).card ≤ (E.filter fun p => Covers q p.2.spec).card +
      pcB (keyOf U (nd U i).ctx) q.2.2.1 q.2.2.2 := by
    unfold coverSet
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
    split
    · next he => rw [he]; exact card_py_le
    · simp
  have h3 : (E.filter fun p => Covers q p.2.spec).card ≤
      (E.filter fun p => cntP q.2.2.1 q.2.2.2 (entOf U I z p) = true).card := by
    refine Finset.card_le_card fun p hp => ?_
    obtain ⟨hpE, hpc⟩ := Finset.mem_filter.1 hp
    exact Finset.mem_filter.2 ⟨hpE, h.cnt_of_covers hpE hpc⟩
  omega

end Star

end ContextCalculus.SRIQ.Fast
