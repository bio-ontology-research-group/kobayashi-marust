import ContextCalculus.SRIQ.FastDefs

/-!
# Certificate check for the fast SHIQ procedure: basic lemmas (stage C1c)

The indexes of `mkIx` mean what their names say (`mem_fwdI`, `mem_relI_upper`,
`mem_relI_lower`, `upS_sound`, `upClosedB_sound`, `closedI_sound`,
`mem_lowAt`, `mem_uppAt`); every closed superset of a seed contains a
member of `br` (`br_guided`); the depth-first search finds a multiset of
entries exactly when one exists (`dfs_sound`, `dfs_complete`).
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat} {O : Ontology (Fin n) (Fin m)}

/-! ## The indexes -/

theorem mem_allBy {a c : Fin n} {S : RoleT (Fin m)} :
    (S, c) ∈ getL (mkIx O).allBy a.val ↔ Clause.allRight a S c ∈ O := by
  simp only [mkIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨cl, hcl, hf⟩
    cases cl <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨h1, rfl, rfl⟩ := hf
    rw [Fin.ext h1] at hcl
    exact hcl
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_fwdI {t : Ty n} {L : Lab m} {c : Fin n} :
    c ∈ fwdI (mkIx O) t L ↔ ∃ a ∈ t, ∃ S ∈ L, Clause.allRight a S c ∈ O := by
  simp only [fwdI, Finset.mem_biUnion, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, ⟨S, c'⟩, ⟨hm, hS⟩, rfl⟩
    exact ⟨a, ha, S, hS, mem_allBy.1 hm⟩
  · rintro ⟨a, ha, S, hS, hcl⟩
    exact ⟨a, ha, (S, c), ⟨mem_allBy.2 hcl, hS⟩, rfl⟩

theorem fwdI_mono {t t' : Ty n} {L L' : Lab m} (ht : t ⊆ t') (hL : L ⊆ L') :
    fwdI (mkIx O) t L ⊆ fwdI (mkIx O) t' L' := by
  intro c hc
  obtain ⟨a, ha, S, hS, hcl⟩ := mem_fwdI.1 hc
  exact mem_fwdI.2 ⟨a, ht ha, S, hL hS, hcl⟩

theorem mem_relBy {S : RoleT (Fin m)} {b : Fin n} :
    b ∈ getL (mkIx O).relBy (rc S) ↔ (rc S, b) ∈ relSrc O := by
  simp only [mkIx]
  rw [mem_buildIdx (rc_lt S)]
  simp

theorem mem_relI_upper {L : Lab m} {q : Fin n × Nat × RoleT (Fin m) × Fin n}
    (hq : q ∈ upperL O) (hS : q.2.2.1 ∈ L) : q.2.2.2 ∈ relI (mkIx O) L := by
  simp only [relI, Finset.mem_biUnion, List.mem_toFinset]
  refine ⟨_, hS, mem_relBy.2 (List.mem_append_right _ (List.mem_map.2 ⟨q, hq, rfl⟩))⟩

theorem mem_relI_lower {L : Lab m} {q : Fin n × Nat × RoleT (Fin m) × Fin n}
    (hq : q ∈ lowerL O) (hk : 1 ≤ q.2.1) (hR : q.2.2.1 ∈ L) : q.2.2.2 ∈ relI (mkIx O) L := by
  simp only [relI, Finset.mem_biUnion, List.mem_toFinset]
  refine ⟨_, hR, mem_relBy.2 (List.mem_append_left _ (List.mem_filterMap.2 ⟨q, hq, ?_⟩))⟩
  simp [hk]

theorem mem_steps {R S : RoleT (Fin m)} :
    (R, S) ∈ steps O ↔ SRI.RoleStep (sriPart O) R S := by
  simp only [steps, List.mem_flatMap, SRI.RoleStep, mem_sriPart, ofSRI]
  constructor
  · rintro ⟨cl, hcl, hm⟩
    match cl, hcl, hm with
    | .chain [R'] S', hcl, hm =>
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl hcl
      · right; simpa using hcl
  · rintro (h | h)
    · exact ⟨_, h, by simp⟩
    · exact ⟨_, h, by simp⟩

theorem mem_stepsBy {R S : RoleT (Fin m)} :
    S ∈ getL (mkIx O).stepsBy (rc R) ↔ SRI.RoleStep (sriPart O) R S := by
  simp only [mkIx]
  rw [mem_buildIdx (rc_lt R), ← mem_steps]
  constructor
  · rintro ⟨⟨R', S'⟩, h, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [rc_inj h1] at h
    exact h
  · intro h
    exact ⟨_, h, rfl⟩

theorem upAux_sound {R : RoleT (Fin m)} : ∀ (f : Nat) (acc : Lab m) (q : List (RoleT (Fin m))),
    (∀ S ∈ acc, RoleLe O R S) → (∀ S ∈ q, RoleLe O R S) →
    ∀ S ∈ upAux (mkIx O).stepsBy f acc q, RoleLe O R S
  | 0, acc, q, hacc, _ => by simpa [upAux] using hacc
  | _ + 1, acc, [], hacc, _ => by simpa [upAux] using hacc
  | f + 1, acc, x :: rest, hacc, hq => by
    simp only [upAux]
    have hx : RoleLe O R x := hq x List.mem_cons_self
    have hnw : ∀ S ∈ (getL (mkIx O).stepsBy (rc x)).filter (fun S => S ∉ acc), RoleLe O R S := by
      intro S hS
      have h1 := mem_stepsBy.1 (List.mem_filter.1 hS).1
      exact RoleLe.trans hx (Relation.ReflTransGen.single h1)
    refine upAux_sound f _ _ ?_ ?_
    · intro S hS
      rcases Finset.mem_union.1 hS with h | h
      · exact hacc S h
      · exact hnw S (List.mem_toFinset.1 h)
    · intro S hS
      rcases List.mem_append.1 hS with h | h
      · exact hnw S h
      · exact hq S (List.mem_cons_of_mem _ h)

theorem ofRc_rc (R : RoleT (Fin m)) (h : rc R < 2 * m) : ofRc (rc R) h = R :=
  rc_inj (rc_ofRc _ h)

theorem upS_sound {R S : RoleT (Fin m)} (h : S ∈ upS (mkIx O) R) : RoleLe O R S := by
  simp only [upS, mkIx, Array.getElem?_ofFn, rc_lt R, dite_true, Option.getD_some] at h
  rw [ofRc_rc] at h
  refine upAux_sound _ _ _ ?_ ?_ S h
  · intro S hS
    rw [Finset.mem_singleton.1 hS]
    exact Relation.ReflTransGen.refl
  · intro S hS
    rw [List.mem_singleton.1 hS]
    exact Relation.ReflTransGen.refl

theorem upClosedB_sound {L : Lab m} (h : upClosedB (mkIx O) L) : UpClosed O L := by
  intro R hR S hRS
  induction hRS with
  | refl => exact hR
  | tail _ hst ih => exact h _ ih _ (mem_stepsBy.2 hst)

theorem upClosed_flipL {L : Lab m} (h : UpClosed O L) : UpClosed O (flipL L) := by
  intro R hR S hRS
  rw [mem_flipL] at hR ⊢
  exact h _ hR _ (roleLe_flip hRS)

theorem gciArr_mem {i : Nat} {g : List (Fin n) × List (Fin n)}
    (h : (mkIx O).gciArr[i]? = some g) : Clause.gci g.1 g.2 ∈ O := by
  simp only [mkIx, List.getElem?_toArray] at h
  have hm := List.mem_of_getElem? h
  simp only [gciL, List.mem_filterMap] at hm
  obtain ⟨cl, hcl, he⟩ := hm
  cases cl <;> simp only [reduceCtorEq, Option.some.injEq] at he
  subst he
  exact hcl

theorem exists_gciArr {body head : List (Fin n)} (h : Clause.gci body head ∈ O) :
    ∃ i, (mkIx O).gciArr[i]? = some (body, head) ∧ ((body, head), i) ∈ (gciL O).zipIdx := by
  have hm : (body, head) ∈ gciL O := List.mem_filterMap.2 ⟨_, h, rfl⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
  refine ⟨i, ?_, List.mem_zipIdx_iff_getElem?.2 hi⟩
  simpa [mkIx] using hi

theorem closedI_sound {t : Ty n} (h : closedI (mkIx O) t) : Closed O t := by
  rw [closed_iff]
  intro body head hcl hbody
  obtain ⟨i, hi, hz⟩ := exists_gciArr hcl
  have hg : gciAt (mkIx O) i = (body, head) := by simp [gciAt, hi]
  cases body with
  | nil =>
    have := h.1 i (by
      simp only [mkIx, List.mem_map, List.mem_filter]
      exact ⟨_, ⟨hz, rfl⟩, rfl⟩)
    rw [hg] at this
    exact this
  | cons a body =>
    have := h.2 a (hbody a List.mem_cons_self) i ?_ (by rw [hg]; exact hbody)
    · rw [hg] at this
      exact this
    simp only [mkIx]
    rw [mem_buildIdx a.isLt]
    refine ⟨(a.val, i), List.mem_flatMap.2 ⟨_, hz, ?_⟩, rfl⟩
    simp

theorem mem_lowBy {a : Fin n} {q : Nat × RoleT (Fin m) × Fin n} :
    q ∈ getL (mkIx O).lowBy a.val ↔ (a, q) ∈ lowerL O := by
  simp only [mkIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨x, hx, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = x.1 from Fin.ext h1.symm]
    exact hx
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_uppBy {a : Fin n} {q : Nat × RoleT (Fin m) × Fin n} :
    q ∈ getL (mkIx O).uppBy a.val ↔ (a, q) ∈ upperL O := by
  simp only [mkIx]
  rw [mem_buildIdx a.isLt]
  constructor
  · rintro ⟨x, hx, he⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨h1, rfl⟩ := he
    rw [show a = x.1 from Fin.ext h1.symm]
    exact hx
  · intro h
    exact ⟨_, h, rfl⟩

theorem mem_lowAt {t : Ty n} {q : Fin n × Nat × RoleT (Fin m) × Fin n} :
    q ∈ lowAt (mkIx O) t ↔ q ∈ lowerL O ∧ q.1 ∈ t := by
  simp only [lowAt, List.mem_flatMap, Finset.mem_sort, List.mem_map]
  constructor
  · rintro ⟨a, ha, q', hq', rfl⟩
    exact ⟨mem_lowBy.1 hq', ha⟩
  · rintro ⟨hq, ha⟩
    exact ⟨q.1, ha, q.2, mem_lowBy.2 hq, rfl⟩

theorem mem_uppAt {t : Ty n} {q : Fin n × Nat × RoleT (Fin m) × Fin n} :
    q ∈ uppAt (mkIx O) t ↔ q ∈ upperL O ∧ q.1 ∈ t := by
  simp only [uppAt, List.mem_flatMap, Finset.mem_sort, List.mem_map]
  constructor
  · rintro ⟨a, ha, q', hq', rfl⟩
    exact ⟨mem_uppBy.1 hq', ha⟩
  · rintro ⟨hq, ha⟩
    exact ⟨q.1, ha, q.2, mem_uppBy.2 hq, rfl⟩

theorem mem_tops {e : Fin n} (h : e ∈ (mkIx O).tops) :
    ∃ head : List (Fin n), Clause.gci [] head ∈ O ∧ head ≠ [] ∧ ∀ x ∈ head, x = e := by
  simp only [mkIx, List.mem_toFinset, List.mem_filterMap] at h
  obtain ⟨⟨body, head⟩, hg, he⟩ := h
  have hcl : Clause.gci body head ∈ O := by
    simp only [gciL, List.mem_filterMap] at hg
    obtain ⟨cl, hcl, he'⟩ := hg
    cases cl <;> simp only [reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at he'
    obtain ⟨rfl, rfl⟩ := he'
    exact hcl
  match body, head, hcl, he with
  | [], e' :: head, hcl, he =>
    simp only [topName] at he
    split at he
    · next hall =>
      simp only [Option.some.injEq] at he
      subst he
      refine ⟨_, hcl, List.cons_ne_nil _ _, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · simpa using List.all_eq_true.1 hall x hx
    · exact absurd he (by simp)

/-! ## Branches -/

theorem brAux_guided {T : Ty n} (hT : Closed O T) :
    ∀ (f : Nat) (cur : Ty n) (acc q : List Nat), cur ⊆ T → ∃ b ∈ brAux (mkIx O) f cur acc q, b ⊆ T := by
  intro f cur acc q hcur
  induction f, cur, acc, q using brAux.induct (ix := mkIx O) with
  | case1 cur acc q => exact ⟨cur, by simp [brAux], hcur⟩
  | case2 f cur acc => exact ⟨cur, by simp [brAux], hcur⟩
  | case3 f cur acc i rest hg ih =>
    rw [brAux, hg]
    exact ih hcur
  | case4 f cur acc i rest g hg hfire ih =>
    simp only [brAux, hg]
    rw [if_pos hfire]
    obtain ⟨b, hb, hbT⟩ := closed_iff.1 hT g.1 g.2 (gciArr_mem hg)
      fun a ha => hcur (hfire.1 a ha)
    obtain ⟨b', hb', hb'T⟩ := ih b (Finset.insert_subset hbT hcur)
    exact ⟨b', List.mem_flatMap.2 ⟨b, hb, hb'⟩, hb'T⟩
  | case5 f cur acc i rest g hg hfire ih =>
    simp only [brAux, hg]
    rw [if_neg hfire]
    exact ih hcur

theorem br_guided {T s : Ty n} (hT : Closed O T) (hs : s ⊆ T) :
    ∃ b ∈ br (mkIx O) s, b ⊆ T :=
  brAux_guided hT _ _ _ _ hs

/-! ## The search -/

/-- `E` meets the needs and stays within the limits. -/
def Sol (E : List (Lab m × Ty n)) (needs lims : List (RoleT (Fin m) × Fin n × Nat)) : Prop :=
  (∀ x ∈ needs, x.2.2 ≤ E.countP (cntP x.1 x.2.1)) ∧
  (∀ y ∈ lims, E.countP (cntP y.1 y.2.1) ≤ y.2.2)

theorem mem_subC {c : Lab m × Ty n} {l : List (RoleT (Fin m) × Fin n × Nat)}
    {x : RoleT (Fin m) × Fin n × Nat} (hx : x ∈ l) :
    (x.1, x.2.1, if cntP x.1 x.2.1 c then x.2.2 - 1 else x.2.2) ∈ subC c l :=
  List.mem_map.2 ⟨x, hx, rfl⟩

theorem dfs_sound {cs : List (Lab m × Ty n)} : ∀ (f : Nat) (needs lims : List (RoleT (Fin m) × Fin n × Nat)),
    dfs cs f needs lims = true → ∃ E, (∀ c ∈ E, c ∈ cs) ∧ Sol E needs lims := by
  intro f
  induction f with
  | zero =>
    intro needs lims h
    rw [dfs] at h
    split at h
    · next hn =>
      refine ⟨[], by simp, fun x hx => ?_, fun y _ => by simp⟩
      have := List.find?_eq_none.1 hn x hx
      simp only [decide_eq_true_eq, not_lt] at this
      simp [this]
    · simp at h
  | succ f ih =>
    intro needs lims h
    rw [dfs] at h
    split at h
    · next hn =>
      refine ⟨[], by simp, fun x hx => ?_, fun y _ => by simp⟩
      have := List.find?_eq_none.1 hn x hx
      simp only [decide_eq_true_eq, not_lt] at this
      simp [this]
    · obtain ⟨c, hc, hall⟩ := List.any_eq_true.1 h
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at hall
      obtain ⟨⟨_, hlim⟩, hrec⟩ := hall
      obtain ⟨E, hE, hs1, hs2⟩ := ih _ _ hrec
      refine ⟨c :: E, fun c' hc' => ?_, fun x hx => ?_, fun y hy => ?_⟩
      · rcases List.mem_cons.1 hc' with rfl | h'
        · exact hc
        · exact hE c' h'
      · have := hs1 _ (mem_subC (c := c) hx)
        simp only [List.countP_cons]
        split at this <;> simp_all <;> omega
      · have := hs2 _ (mem_subC (c := c) hy)
        simp only [List.countP_cons]
        rcases hlim y hy with h0 | h0
        · simp only [h0, Bool.false_eq_true, ↓reduceIte, add_zero] at this ⊢
          exact this
        · split at this <;> simp_all <;> omega

theorem sum_subC_lt {c : Lab m × Ty n} : ∀ (l : List (RoleT (Fin m) × Fin n × Nat))
    (x : RoleT (Fin m) × Fin n × Nat), x ∈ l → cntP x.1 x.2.1 c = true → 0 < x.2.2 →
    ((subC c l).map (·.2.2)).sum < (l.map (·.2.2)).sum
  | [], _, hx, _, _ => by simp at hx
  | y :: l, x, hx, hc, hpos => by
    have hle : ∀ l : List (RoleT (Fin m) × Fin n × Nat),
        ((subC c l).map (·.2.2)).sum ≤ (l.map (·.2.2)).sum := by
      intro l
      induction l with
      | nil => simp [subC]
      | cons z l ih =>
        simp only [subC, List.map_cons, List.sum_cons] at ih ⊢
        split <;> omega
    simp only [subC, List.map_cons, List.sum_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [if_pos hc]
      have := hle l
      simp only [subC] at this
      omega
    · have := sum_subC_lt l x hx hc hpos
      simp only [subC] at this
      split <;> omega

theorem dfs_complete {cs : List (Lab m × Ty n)} : ∀ (f : Nat) (needs lims : List (RoleT (Fin m) × Fin n × Nat))
    (E : List (Lab m × Ty n)), (∀ c ∈ E, c ∈ cs) → Sol E needs lims →
    (needs.map (·.2.2)).sum < f → dfs cs f needs lims = true := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ h; omega
  | succ f ih =>
    intro needs lims E hE hS hf
    rw [dfs]
    split
    · rfl
    · next x hx =>
      have hxm := List.mem_of_find?_eq_some hx
      have hxp : 0 < x.2.2 := by simpa using List.find?_some hx
      have hcnt := hS.1 x hxm
      obtain ⟨c, hcE, hcx⟩ := List.countP_pos_iff.1 (lt_of_lt_of_le hxp hcnt)
      refine List.any_eq_true.2 ⟨c, hE c hcE, ?_⟩
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_true_eq]
      refine ⟨⟨hcx, fun y hy => ?_⟩, ?_⟩
      · by_cases hy0 : cntP y.1 y.2.1 c = true
        · right
          have h1 := hS.2 y hy
          have h2 : 0 < E.countP (cntP y.1 y.2.1) := List.countP_pos_iff.2 ⟨c, hcE, hy0⟩
          omega
        · left; simpa using hy0
      · refine ih _ _ (E.erase c) (fun c' hc' => hE c' (List.mem_of_mem_erase hc')) ⟨?_, ?_⟩ ?_
        · intro x' hx'
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx'
          have h1 := hS.1 z hz
          rw [List.countP_erase]
          by_cases hzc : cntP z.1 z.2.1 c = true
          · simp only [hcE, hzc, and_self, if_true]; omega
          · simp only [hzc, and_false, if_false, Bool.false_eq_true]; omega
        · intro y' hy'
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy'
          have h1 := hS.2 z hz
          rw [List.countP_erase]
          by_cases hzc : cntP z.1 z.2.1 c = true
          · simp only [hcE, hzc, and_self, if_true]; omega
          · simp only [hzc, and_false, if_false, Bool.false_eq_true]; omega
        · have := sum_subC_lt needs x hxm hcx hxp
          omega

/-! ## Deduplication by key -/

theorem dedupAux_subset {α β : Type} [DecidableEq β] [Hashable β] (key : α → β) :
    ∀ (l acc : List α) (h : Std.HashSet β), ∀ x ∈ dedupAux key l acc h, x ∈ l ∨ x ∈ acc
  | [], acc, h, x, hx => by simp [dedupAux] at hx; exact Or.inr hx
  | y :: l, acc, h, x, hx => by
    simp only [dedupAux] at hx
    split at hx
    · rcases dedupAux_subset key l acc h x hx with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · exact Or.inr h1
    · rcases dedupAux_subset key l _ _ x hx with h1 | h1
      · exact Or.inl (List.mem_cons_of_mem _ h1)
      · rcases List.mem_cons.1 h1 with rfl | h1
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h1

theorem dedupKey_subset {α β : Type} [DecidableEq β] [Hashable β] (key : α → β)
    (l : List α) : ∀ x ∈ dedupKey key l, x ∈ l := by
  intro x hx
  rcases dedupAux_subset key l [] ∅ x hx with h | h
  · exact h
  · simp at h

theorem dedupAux_spec {α β : Type} [DecidableEq β] [Hashable β] (key : α → β) :
    ∀ (l acc : List α) (h : Std.HashSet β), (∀ b, h.contains b = true → ∃ y ∈ acc, key y = b) →
      (∀ y ∈ acc, y ∈ dedupAux key l acc h) ∧
      ∀ x ∈ l, ∃ y ∈ dedupAux key l acc h, key y = key x
  | [], acc, h, _ => ⟨fun y hy => by simpa [dedupAux] using hy, fun x hx => by simp at hx⟩
  | z :: l, acc, h, hinv => by
    simp only [dedupAux]
    split
    · next hc =>
      obtain ⟨h1, h2⟩ := dedupAux_spec key l acc h hinv
      refine ⟨h1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · obtain ⟨y, hy, hk⟩ := hinv _ hc
        exact ⟨y, h1 y hy, hk⟩
      · exact h2 x hx
    · next hc =>
      have hinv' : ∀ b, (h.insert (key z)).contains b = true → ∃ y ∈ z :: acc, key y = b := by
        intro b hb
        rw [Std.HashSet.contains_insert] at hb
        simp only [Bool.or_eq_true, beq_iff_eq] at hb
        rcases hb with hb | hb
        · exact ⟨z, List.mem_cons_self, hb⟩
        · obtain ⟨y, hy, hk⟩ := hinv b hb
          exact ⟨y, List.mem_cons_of_mem _ hy, hk⟩
      obtain ⟨h1, h2⟩ := dedupAux_spec key l (z :: acc) _ hinv'
      refine ⟨fun y hy => h1 y (List.mem_cons_of_mem _ hy), fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨x, h1 x List.mem_cons_self, rfl⟩
      · exact h2 x hx

theorem exists_dedupKey {α β : Type} [DecidableEq β] [Hashable β] (key : α → β)
    (l : List α) : ∀ x ∈ l, ∃ y ∈ dedupKey key l, key y = key x :=
  (dedupAux_spec key l [] ∅ fun b hb => by simp at hb).2

/-- Replacing each entry by one with the same counts on `needs` and `lims`
keeps a solution. -/
theorem sol_dedup {cs : List (Lab m × Ty n)} {needs lims : List (RoleT (Fin m) × Fin n × Nat)} :
    ∀ E : List (Lab m × Ty n), (∀ c ∈ E, c ∈ cs) →
      ∃ E' : List (Lab m × Ty n), (∀ c ∈ E', c ∈ dedupKey (fun c =>
          (needs.map fun x => cntP x.1 x.2.1 c, lims.map fun x => cntP x.1 x.2.1 c)) cs) ∧
        (∀ x ∈ needs, E'.countP (cntP x.1 x.2.1) = E.countP (cntP x.1 x.2.1)) ∧
        (∀ x ∈ lims, E'.countP (cntP x.1 x.2.1) = E.countP (cntP x.1 x.2.1))
  | [], _ => ⟨[], by simp, by simp, by simp⟩
  | c :: E, hE => by
    obtain ⟨E', h1, h2, h3⟩ := sol_dedup E fun c' h => hE c' (List.mem_cons_of_mem _ h)
    obtain ⟨c', hc', hk⟩ := exists_dedupKey (fun c =>
      (needs.map fun x => cntP x.1 x.2.1 c, lims.map fun x => cntP x.1 x.2.1 c)) cs c
      (hE c List.mem_cons_self)
    simp only [Prod.mk.injEq, List.map_inj_left] at hk
    refine ⟨c' :: E', fun d hd => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact hc'
      · exact h1 d hd
    · simp only [List.countP_cons, h2 x hx, hk.1 x hx]
    · simp only [List.countP_cons, h3 x hx, hk.2 x hx]

end ContextCalculus.SRIQ.Fast
