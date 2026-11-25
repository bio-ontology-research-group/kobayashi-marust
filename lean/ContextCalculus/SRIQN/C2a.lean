import ContextCalculus.SRIQN.Forest

/-!
# Stage C2a: completeness without inverse-counted needs (design section 7)

`docs/V1.7.0-C2-NOMINALS-DESIGN.md`. Under `IsC2a`, a model, first
shrunk so that nominal-only names hold at nominal elements only
(`shrinkI`), gives a
realisation whose core is the set of nominal elements (one arbitrary
element when there is no nominal name). A non-core element `x` reached
from a parent `y` becomes a record with

* core entries: to each core element `d ≠ y`, the model label restricted
  to the roles above a role of a lower clause at `x` (`UpX`);
* children: its witnesses outside the core and other than `y`.

A restricted core entry never counts at the core element: that would need
a lower clause at `x` with a role below the inverse of an at-most role,
and the subject of that clause is neither a nominal name nor nominal-only,
since `x` is not a nominal element. `IsC2a` excludes it.

`consistentN_iff_c2a`: for ALCHOIQ and C2a, consistency is the existence
of a realisation over `Fin k` with `0 < k ≤ max 1 |Nom O|` whose core
elements each carry a nominal name (when there is one).
-/

namespace ContextCalculus.SRIQN

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ (Nbr StarOK UpClosed EdgeOK cnt flipL nbrs RoleLe Closed mem_flipL
  typeOf labelOf mem_typeOf mem_labelOf flipL_labelOf wit wit_ex wit_atLeast entry lowerL upperL
  mem_lowerL mem_upperL)

variable {CName Role D : Type}

section Model

set_option linter.unusedSectionVars false

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable {B : SRIQ.Ontology CName Role} (I : Interp D CName Role)

/-- The star of `x` over the distinct neighbours `E` with labels `lb`
inside the model labels is `StarOK` when every witness of a lower clause
at `x` is in `E` with the clause's role in its label. -/
theorem starOK_of_sub (hI : SRIQ.models I B) (x : D) (E : List D) (hnd : E.Nodup)
    (lb : D → Finset (RoleT Role)) (hsub : ∀ z ∈ E, lb z ⊆ labelOf I x z)
    (hup : ∀ z ∈ E, UpClosed B (lb z))
    (hw : ∀ q ∈ lowerL B, q.1 ∈ typeOf I x → ∀ y ∈ wit B I x, I.rt q.2.2.1 x y →
      y ∈ E ∧ q.2.2.1 ∈ lb y) :
    StarOK B (typeOf I x) (E.map fun z => (lb z, typeOf I z)) := by
  classical
  have hc : ∀ R b, cnt (E.map fun z => (lb z, typeOf I z)) R b =
      E.countP (fun z => decide (R ∈ lb z ∧ I.c b z)) := by
    intro R b
    unfold cnt
    rw [List.countP_map]
    refine List.countP_congr fun z _ => ?_
    simp [mem_typeOf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [SRIQ.closed_iff]
    intro body head hcl hbody
    obtain ⟨b, hb, hbx⟩ := hI _ hcl x fun a ha => (mem_typeOf I).1 (hbody a ha)
    exact ⟨b, hb, (mem_typeOf I).2 hbx⟩
  · intro e he
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 he
    refine ⟨hup z hz, fun a S c hcl => ⟨fun hS ha => ?_, fun hS ha => ?_⟩⟩
    · have hS' := (mem_labelOf I).1 (hsub z hz hS)
      exact (mem_typeOf I).2 (hI _ hcl x ((mem_typeOf I).1 ha) z hS')
    · have hS' := (mem_labelOf I).1 (hsub z hz hS)
      rw [SRI.Interp.rt_flip] at hS'
      exact (mem_typeOf I).2 (hI _ hcl z ((mem_typeOf I).1 ha) x hS')
  · intro a R b hcl ha
    rw [hc]
    obtain ⟨y, hy, hP⟩ := wit_ex I hcl (hI _ hcl x ((mem_typeOf I).1 ha))
    obtain ⟨hyE, hR⟩ := hw (a, 1, R, b) (mem_lowerL.2 (Or.inl ⟨rfl, hcl⟩)) ha y hy hP.1
    exact List.countP_pos_iff.2 ⟨y, hyE, by simpa using ⟨hR, hP.2⟩⟩
  · intro a k R b hcl ha
    rw [hc]
    obtain ⟨l, hnd', hlen, hP, hsub'⟩ := wit_atLeast I hcl (hI _ hcl x ((mem_typeOf I).1 ha))
    rw [← hlen]
    refine SRIQ.length_le_countP hnd' (fun y hy => ?_) fun y hy => ?_
    · have := hw (a, k, R, b) (mem_lowerL.2 (Or.inr hcl)) ha y (hsub' hy) (hP y hy).1
      simpa using ⟨this.2, (hP y hy).2⟩
    · exact (hw (a, k, R, b) (mem_lowerL.2 (Or.inr hcl)) ha y (hsub' hy) (hP y hy).1).1
  · intro a k R b hcl ha
    rw [hc, List.countP_eq_length_filter]
    refine hI _ hcl x ((mem_typeOf I).1 ha) _ (hnd.filter _) fun y hy => ?_
    have h := of_decide_eq_true (List.mem_filter.1 hy).2
    exact ⟨(mem_labelOf I).1 (hsub y (List.mem_filter.1 hy).1 h.1), h.2⟩

theorem upClosed_labelOf (hI : SRIQ.models I B) (x y : D) : UpClosed B (labelOf I x y) :=
  fun _ hR _ hRS => (mem_labelOf I).2 (SRIQ.roleLe_sound hI hRS _ _ ((mem_labelOf I).1 hR))

variable (B) in
/-- The roles above a role of a lower clause at `x`. -/
noncomputable def UpX (x : D) : Finset (RoleT Role) := by
  classical
  exact Finset.univ.filter fun T => ∃ q ∈ lowerL B, q.1 ∈ typeOf I x ∧ RoleLe B q.2.2.1 T

theorem mem_UpX {x : D} {T : RoleT Role} :
    T ∈ UpX B I x ↔ ∃ q ∈ lowerL B, q.1 ∈ typeOf I x ∧ RoleLe B q.2.2.1 T := by
  classical
  simp [UpX]

theorem upClosed_UpX (x : D) : UpClosed B (UpX B I x) := by
  intro R hR S hRS
  obtain ⟨q, hq, ha, hle⟩ := (mem_UpX I).1 hR
  exact (mem_UpX I).2 ⟨q, hq, ha, SRIQ.RoleLe.trans hle hRS⟩

theorem upClosed_inter {L L' : Finset (RoleT Role)} (h : UpClosed B L) (h' : UpClosed B L') :
    UpClosed B (L ∩ L') := by
  intro R hR S hRS
  rw [Finset.mem_inter] at hR ⊢
  exact ⟨h _ hR.1 _ hRS, h' _ hR.2 _ hRS⟩

end Model

/-! ## Shrinking nominal-only names -/

section Shrink

open Classical

variable {O : Ontology CName Role} (I : Interp D CName Role)

/-- `I` with every nominal-only name shrunk to the elements of the nominal
names that imply it. -/
noncomputable def shrinkI (O : Ontology CName Role) (I : Interp D CName Role) :
    Interp D CName Role :=
  ⟨fun X y => if NomOnly O X then ∃ a ∈ noms O, SRIQ.Clause.gci [a] [X] ∈ basePart O ∧ I.c a y
    else I.c X y, I.r⟩

theorem shrinkI_c_of_not {X : CName} (h : ¬ NomOnly O X) (y : D) :
    (shrinkI O I).c X y ↔ I.c X y := by
  simp only [shrinkI, if_neg h]

theorem shrinkI_rt (R : RoleT Role) (x y : D) : (shrinkI O I).rt R x y ↔ I.rt R x y := by
  cases R <;> exact Iff.rfl

theorem shrinkI_path : ∀ (body : List (RoleT Role)) (x y : D),
    (shrinkI O I).path body x y ↔ I.path body x y
  | [], x, y => Iff.rfl
  | R :: Rs, x, z => by
    simp only [SRI.Interp.path, shrinkI_rt, shrinkI_path Rs]

theorem nom_not_nomOnly {a : CName} (ha : a ∈ noms O) : ¬ NomOnly O a := fun h => h.1 ha

variable {I}

theorem shrinkI_sub (hI : SRIQ.models I (basePart O)) {X : CName} {y : D}
    (h : (shrinkI O I).c X y) : I.c X y := by
  by_cases hX : NomOnly O X
  · simp only [shrinkI, if_pos hX] at h
    obtain ⟨a, -, hg, hay⟩ := h
    obtain ⟨b, hb, hby⟩ := hI _ hg y (by simpa using hay)
    simp only [List.mem_singleton] at hb
    exact hb ▸ hby
  · exact (shrinkI_c_of_not I hX y).1 h

theorem shrinkI_nomOnly {X : CName} (hX : NomOnly O X) {y : D} (h : (shrinkI O I).c X y) :
    ∃ a ∈ noms O, I.c a y := by
  simp only [shrinkI, if_pos hX] at h
  obtain ⟨a, ha, -, hay⟩ := h
  exact ⟨a, ha, hay⟩

/-- **Shrinking keeps models.** -/
theorem shrinkI_models (hI : models I O) : models (shrinkI O I) O := by
  obtain ⟨hb, hn⟩ := models_iff.1 hI
  have notb : ∀ {b : CName}, (∃ cl ∈ basePart O, ¬ PosOK (noms O) b cl) → ¬ NomOnly O b :=
    fun ⟨cl, hcl, hp⟩ h => hp (h.2 cl hcl)
  refine models_iff.2 ⟨fun cl hcl => ?_, fun a ha => ?_⟩
  · cases cl with
    | gci body head =>
      intro x hbody
      by_cases hX : ∃ X ∈ head, NomOnly O X
      · obtain ⟨X, hXh, hX⟩ := hX
        obtain ⟨a, ha, rfl, rfl⟩ := hX.2 _ hcl hXh
        refine ⟨X, List.mem_singleton_self _, ?_⟩
        simp only [shrinkI, if_pos hX]
        exact ⟨a, ha, hcl, (shrinkI_c_of_not I (nom_not_nomOnly ha) x).1 (hbody a (by simp))⟩
      · push Not at hX
        obtain ⟨b, hb, hbx⟩ := hb _ hcl x fun a ha => shrinkI_sub hb (hbody a ha)
        exact ⟨b, hb, (shrinkI_c_of_not I (hX b hb) x).2 hbx⟩
    | exRight a R b =>
      intro x hx
      obtain ⟨y, hy, hby⟩ := hb _ hcl x (shrinkI_sub hb hx)
      exact ⟨y, (shrinkI_rt I R x y).2 hy,
        (shrinkI_c_of_not I (notb ⟨_, hcl, fun h => h rfl⟩) y).2 hby⟩
    | allRight a R b =>
      intro x hx y hy
      exact (shrinkI_c_of_not I (notb ⟨_, hcl, fun h => h rfl⟩) y).2
        (hb _ hcl x (shrinkI_sub hb hx) y ((shrinkI_rt I R x y).1 hy))
    | atLeast a k R b =>
      intro x hx
      obtain ⟨l, hnd, hlen, hl⟩ := hb _ hcl x (shrinkI_sub hb hx)
      exact ⟨l, hnd, hlen, fun y hy => ⟨(shrinkI_rt I R x y).2 (hl y hy).1,
        (shrinkI_c_of_not I (notb ⟨_, hcl, fun h => h rfl⟩) y).2 (hl y hy).2⟩⟩
    | atMost a k R b =>
      intro x hx l hnd hl
      exact hb _ hcl x (shrinkI_sub hb hx) l hnd fun y hy =>
        ⟨(shrinkI_rt I R x y).1 (hl y hy).1, shrinkI_sub hb (hl y hy).2⟩
    | chain body S =>
      intro x y hp
      exact (shrinkI_rt I S x y).2 (hb _ hcl x y ((shrinkI_path I body x y).1 hp))
  · obtain ⟨x, hx⟩ := hn a ha
    exact ⟨x, fun y => (shrinkI_c_of_not I (nom_not_nomOnly ha) y).trans (hx y)⟩

end Shrink

section Real

set_option linter.unusedSectionVars false

open Classical

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]
variable {O : Ontology CName Role} (I : Interp D CName Role) {K : Type} [Fintype K]
  (v : K → D)

/-- The record of `x` with parent `y`. -/
noncomputable def recM (x y : D) : RecN CName Role K :=
  (typeOf I x, if h : ∃ c, v c = y then .inr (h.choose, labelOf I x y)
    else .inl (labelOf I x y, typeOf I y))

/-- The core entries of `x` with parent `y`. -/
noncomputable def ceM (x y : D) (d : K) : Finset (RoleT Role) :=
  if v d = y then ∅ else labelOf I x (v d) ∩ UpX (basePart O) I x

/-- The tree children of `x` with parent `y`. -/
noncomputable def kidsM (x y : D) : List D :=
  (wit (basePart O) I x).dedup.filter fun z => decide ((¬ ∃ c, v c = z) ∧ z ≠ y)

/-- The records of the non-core elements. -/
def recsM : Set (RecN CName Role K) :=
  {ρ | ∃ x y, (¬ ∃ c, v c = x) ∧ ρ = recM I v x y}

variable {v} (hv : Function.Injective v)

include hv in
theorem recM_core (x : D) (c : K) : recM I v x (v c) = (typeOf I x, .inr (c, labelOf I x (v c))) := by
  have h : ∃ c', v c' = v c := ⟨c, rfl⟩
  unfold recM
  rw [dif_pos h]
  have := hv h.choose_spec
  simp only [this]

theorem recM_tree (x y : D) (hy : ¬ ∃ c, v c = y) :
    recM I v x y = (typeOf I x, .inl (labelOf I x y, typeOf I y)) := by
  unfold recM
  rw [dif_neg hy]

theorem parentE_recM (x y : D) :
    parentE (fun c => typeOf I (v c)) (recM I v x y).2 = (labelOf I x y, typeOf I y) := by
  unfold recM
  split_ifs with h
  · simp only [parentE]
    rw [h.choose_spec]
  · rfl

variable {S : CName → Prop} (hI : models I O) (hC : IsC2aS O S)
  (hcov : ∀ a ∈ noms O, ∀ x, I.c a x → ∃ c, v c = x)
  (hS : ∀ X, S X → ∀ x, I.c X x → ∃ c, v c = x)

include hv hI hC hcov hS in
theorem recsM_selfSupp :
    SelfSuppN (basePart O) (noms O) (fun c => typeOf I (v c)) (recsM I v) := by
  have hIB := (models_iff.1 hI).1
  rintro ρ ⟨x, y, hx, rfl⟩
  have hxnom : ∀ a ∈ noms O, a ∉ typeOf I x := fun a ha hax =>
    hx (hcov a ha x ((mem_typeOf I).1 hax))
  let lb : D → Finset (RoleT Role) := fun z =>
    if z = y then labelOf I x z else if ∃ c, v c = z then labelOf I x z ∩ UpX (basePart O) I x
    else labelOf I x z
  set cores := (Finset.univ.filter fun d => ceM (O := O) I v x y d ≠ ∅).toList with hcores
  have hmemc : ∀ d, d ∈ cores ↔ ceM (O := O) I v x y d ≠ ∅ := by
    intro d
    rw [hcores, Finset.mem_toList, Finset.mem_filter]
    simp
  have hcne : ∀ d, ceM (O := O) I v x y d ≠ ∅ → v d ≠ y := by
    intro d h he
    exact h (by simp [ceM, he])
  have hlbc : ∀ d, ceM (O := O) I v x y d ≠ ∅ → lb (v d) = ceM (O := O) I v x y d := by
    intro d h
    simp only [lb, ceM, if_neg (hcne d h)]
    rw [if_pos ⟨d, rfl⟩]
  set E := y :: (cores.map v ++ kidsM (O := O) I v x y) with hE
  refine ⟨(ceM (O := O) I v x y, (kidsM (O := O) I v x y).map (entry I x)),
    hxnom, ?_, ?_, ?_, ?_⟩
  · -- the anchor
    intro c L h
    unfold recM at h
    split_ifs at h with hy
    · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [ceM, hy.choose_spec]
  · -- core entries are uncounted
    rintro d ⟨a', k', R', b', hcl, -, hR, -⟩
    dsimp only at hR
    rw [mem_flipL] at hR
    have hne : ceM (O := O) I v x y d ≠ ∅ := fun h0 => by
      rw [h0] at hR
      exact Finset.notMem_empty _ hR
    simp only [ceM, if_neg (hcne d hne), Finset.mem_inter] at hR
    obtain ⟨q, hq, hqx, hle⟩ := (mem_UpX I).1 hR.2
    exact hC q hq (fun hqn => hxnom _ hqn hqx)
      (fun hqo => hx (hS _ hqo x ((mem_typeOf I).1 hqx))) (a', k', R', b') (mem_upperL.2 hcl) hle
  · -- the star
    have hstar := starOK_of_sub I hIB x E ?_ lb ?_ ?_ ?_
    · have heq : E.map (fun z => (lb z, typeOf I z)) =
          (parentE (fun c => typeOf I (v c)) (recM I v x y).2 ::
            cEntries (fun c => typeOf I (v c)) (ceM (O := O) I v x y)) ++
            (kidsM (O := O) I v x y).map (entry I x) := by
        rw [hE, parentE_recM, List.map_cons, List.cons_append, List.map_append]
        simp only [lb, if_true, cEntries, List.map_map, ← hcores]
        congr 1
        congr 1
        · refine List.map_congr_left fun d hd => ?_
          simp only [Function.comp_apply]
          rw [← hlbc d ((hmemc d).1 hd)]
        · refine List.map_congr_left fun z hz => ?_
          have hz' := of_decide_eq_true (List.mem_filter.1 hz).2
          simp only [entry, if_neg hz'.2, if_neg hz'.1]
      rw [← heq]
      exact hstar
    · -- nodup
      rw [hE, List.nodup_cons, List.nodup_append]
      refine ⟨?_, ⟨(Finset.nodup_toList _).map hv, (List.nodup_dedup _).filter _, ?_⟩⟩
      · rw [List.mem_append]
        rintro (h | h)
        · obtain ⟨d, hd, hdy⟩ := List.mem_map.1 h
          exact hcne d ((hmemc d).1 hd) hdy
        · exact (of_decide_eq_true (List.mem_filter.1 h).2).2 rfl
      · intro u hu w hw huw
        subst huw
        obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
        exact (of_decide_eq_true (List.mem_filter.1 hw).2).1 ⟨d, rfl⟩
    · intro z _
      simp only [lb]
      split_ifs
      · exact Finset.Subset.refl _
      · exact Finset.inter_subset_left
      · exact Finset.Subset.refl _
    · intro z _
      simp only [lb]
      split_ifs
      · exact upClosed_labelOf I hIB x z
      · exact upClosed_inter (upClosed_labelOf I hIB x z) (upClosed_UpX I x)
      · exact upClosed_labelOf I hIB x z
    · intro q hq hqx z hz hR
      have hRl : q.2.2.1 ∈ labelOf I x z := (mem_labelOf I).2 hR
      by_cases hzy : z = y
      · subst hzy
        exact ⟨List.mem_cons_self, by simp only [lb, if_true]; exact hRl⟩
      by_cases hzc : ∃ c, v c = z
      · obtain ⟨d, rfl⟩ := hzc
        have hRu : q.2.2.1 ∈ UpX (basePart O) I x :=
          (mem_UpX I).2 ⟨q, hq, hqx, Relation.ReflTransGen.refl⟩
        have hce : q.2.2.1 ∈ ceM (O := O) I v x y d := by
          simp only [ceM, if_neg hzy]
          exact Finset.mem_inter.2 ⟨hRl, hRu⟩
        have hne : ceM (O := O) I v x y d ≠ ∅ := fun h0 => by
          rw [h0] at hce
          exact Finset.notMem_empty _ hce
        refine ⟨List.mem_cons_of_mem _ (List.mem_append_left _
          (List.mem_map.2 ⟨d, (hmemc d).2 hne, rfl⟩)), ?_⟩
        rw [hlbc d hne]
        exact hce
      · refine ⟨List.mem_cons_of_mem _ (List.mem_append_right _
          (List.mem_filter.2 ⟨List.mem_dedup.2 hz, decide_eq_true ⟨hzc, hzy⟩⟩)), ?_⟩
        simp only [lb, if_neg hzy, if_neg hzc]
        exact hRl
  · -- the children
    intro e he
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 he
    have hz' := of_decide_eq_true (List.mem_filter.1 hz).2
    refine ⟨z, x, hz'.1, ?_⟩
    rw [recM_tree I z x hx, childRecN]
    simp [entry, recM, flipL_labelOf]

include hv hI hC hcov hS in
/-- **Model to realisation (C2a).** -/
noncomputable def realOfModelN : RealisationN (basePart O) (noms O) K where
  ty c := typeOf I (v c)
  lab c d := labelOf I (v c) (v d)
  symm c d := (flipL_labelOf I (v c) (v d)).symm
  nom a ha := by
    obtain ⟨x, hx⟩ := (models_iff.1 hI).2 a ha
    obtain ⟨c, rfl⟩ := hcov a ha x ((hx x).2 rfl)
    refine ⟨c, (mem_typeOf I).2 ((hx _).2 rfl), fun c' hc' => hv ?_⟩
    exact (hx _).1 ((mem_typeOf I).1 hc')
  kids c := by
    have hIB := (models_iff.1 hI).1
    let kidsC := (wit (basePart O) I (v c)).dedup.filter fun z => decide (¬ ∃ c, v c = z)
    refine ⟨kidsC.map (entry I (v c)), ?_, fun e he => ?_⟩
    · set L := (Finset.univ.filter fun d => labelOf I (v c) (v d) ≠ ∅).toList with hL
      have heq : nbrs (fun c => typeOf I (v c)) (fun c d => labelOf I (v c) (v d)) c ++
          kidsC.map (entry I (v c)) = (L.map v ++ kidsC).map (entry I (v c)) := by
        simp only [nbrs, List.map_append, List.map_map, hL]
        rfl
      rw [heq]
      refine SRIQ.starOK_of_model I hIB (v c) _ ?_ ?_
      · rw [List.nodup_append]
        refine ⟨(Finset.nodup_toList _).map hv, (List.nodup_dedup _).filter _, ?_⟩
        intro u hu w hw huw
        subst huw
        obtain ⟨d, -, rfl⟩ := List.mem_map.1 hu
        exact (of_decide_eq_true (List.mem_filter.1 hw).2) ⟨d, rfl⟩
      · intro y hy R hR
        by_cases hb : ∃ d, v d = y
        · obtain ⟨d, rfl⟩ := hb
          refine List.mem_append_left _ (List.mem_map.2 ⟨d, ?_, rfl⟩)
          rw [hL, Finset.mem_toList, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun h0 => ?_⟩
          have : R ∈ labelOf I (v c) (v d) := (mem_labelOf I).2 hR
          rw [h0] at this
          exact absurd this (Finset.notMem_empty _)
        · exact List.mem_append_right _ (List.mem_filter.2 ⟨List.mem_dedup.2 hy, decide_eq_true hb⟩)
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.1 he
      have hz' := of_decide_eq_true (List.mem_filter.1 hz).2
      refine ⟨recsM I v, ⟨z, v c, hz', ?_⟩, recsM_selfSupp I hv hI hC hcov hS⟩
      rw [recM_core I hv z c]
      simp [anchorRec, entry, flipL_labelOf]

end Real

/-! ## The characterisation for C2a -/

section Char

variable [Fintype CName] [DecidableEq CName] [Fintype Role] [DecidableEq Role]

/-- **C2a completeness from a model** in which the exempt names `S` hold at
nominal elements only. -/
theorem c2a_complete_of {O : Ontology CName Role} {S : CName → Prop} (hC : IsC2aS O S)
    {D : Type} [Nonempty D] (I : Interp D CName Role) (hI : models I O)
    (hS0 : ∀ X, S X → ∀ x, I.c X x → ∃ a ∈ noms O, I.c a x) :
    ∃ k, 0 < k ∧ k ≤ max 1 (noms O).toFinset.card ∧
      ∃ r : RealisationN (basePart O) (noms O) (Fin k),
        noms O = [] ∨ ∀ c, ∃ a ∈ noms O, a ∈ r.ty c := by
  classical
  obtain ⟨x0⟩ := (inferInstance : Nonempty D)
  have hnom := (models_iff.1 hI).2
  let e : CName → D := fun a => if h : NomAt I a then h.choose else x0
  have he : ∀ a ∈ noms O, ∀ x, I.c a x ↔ x = e a := by
    intro a ha x
    have h := hnom a ha
    simp only [e, dif_pos h]
    exact h.choose_spec x
  let T : Finset D := if noms O = [] then {x0} else (noms O).toFinset.image e
  have hTpos : 0 < T.card := by
    simp only [T]
    split_ifs with h
    · simp
    · obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ h
      exact Finset.card_pos.2 ⟨e a, Finset.mem_image.2 ⟨a, List.mem_toFinset.2 ha, rfl⟩⟩
  have hTle : T.card ≤ max 1 (noms O).toFinset.card := by
    simp only [T]
    split_ifs
    · simp
    · exact le_trans Finset.card_image_le (le_max_right _ _)
  let eq := T.equivFin.symm
  let v : Fin T.card → D := fun c => (eq c).1
  have hv : Function.Injective v := fun c d h => eq.injective (Subtype.ext h)
  have hcov : ∀ a ∈ noms O, ∀ x, I.c a x → ∃ c, v c = x := by
    intro a ha x hx
    have hxT : x ∈ T := by
      have : noms O ≠ [] := fun h => by rw [h] at ha; simp at ha
      simp only [T, if_neg this]
      exact Finset.mem_image.2 ⟨a, List.mem_toFinset.2 ha, ((he a ha x).1 hx).symm⟩
    exact ⟨eq.symm ⟨x, hxT⟩, by simp [v]⟩
  have hS : ∀ X, S X → ∀ x, I.c X x → ∃ c, v c = x := by
    intro X hX x hx
    obtain ⟨a, ha, hax⟩ := hS0 X hX x hx
    exact hcov a ha x hax
  refine ⟨T.card, hTpos, hTle, realOfModelN I hv hI hC hcov hS, ?_⟩
  by_cases hN : noms O = []
  · exact Or.inl hN
  · refine Or.inr fun c => ?_
    have hvT := (eq c).2
    simp only [T, if_neg hN] at hvT
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hvT
    have ha' := List.mem_toFinset.1 ha
    refine ⟨a, ha', ?_⟩
    show a ∈ typeOf I (v c)
    rw [mem_typeOf]
    exact (he a ha' _).2 hae.symm

/-- **C2a completeness.** A consistent C2a ontology has a realisation over
`Fin k`, `0 < k ≤ max 1 |Nom O|`, whose core elements each carry a
nominal name when there is one. -/
theorem c2a_complete {O : Ontology CName Role} (hC : IsC2a O) (hc : ConsistentN O) :
    ∃ k, 0 < k ∧ k ≤ max 1 (noms O).toFinset.card ∧
      ∃ r : RealisationN (basePart O) (noms O) (Fin k),
        noms O = [] ∨ ∀ c, ∃ a ∈ noms O, a ∈ r.ty c := by
  obtain ⟨D, hD, I0, hI0⟩ := hc
  refine c2a_complete_of hC (shrinkI O I0) (shrinkI_models hI0) fun X hX x hx => ?_
  obtain ⟨a, ha, hax⟩ := shrinkI_nomOnly hX hx
  exact ⟨a, ha, (shrinkI_c_of_not I0 (nom_not_nomOnly ha) x).2 hax⟩

/-- **C2a characterisation.** -/
theorem consistentN_iff_c2a {O : Ontology CName Role} (hA : IsALCHOIQ O) (hC : IsC2a O) :
    ConsistentN O ↔ ∃ k, 0 < k ∧ k ≤ max 1 (noms O).toFinset.card ∧
      Nonempty (RealisationN (basePart O) (noms O) (Fin k)) := by
  constructor
  · intro h
    obtain ⟨k, hk, hle, r, -⟩ := c2a_complete hC h
    exact ⟨k, hk, hle, ⟨r⟩⟩
  · rintro ⟨k, hk, -, ⟨r⟩⟩
    haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    exact realisation_sound hA r

end Char

end ContextCalculus.SRIQN

#print axioms ContextCalculus.SRIQN.c2a_complete
#print axioms ContextCalculus.SRIQN.consistentN_iff_c2a
