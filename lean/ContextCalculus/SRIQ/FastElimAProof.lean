import ContextCalculus.SRIQ.FastCheckAProof
import ContextCalculus.SRIQ.FastElimA
import ContextCalculus.SRIQ.FastCheck

/-!
# Certificate check for the fast SHIQ procedure: the worklist elimination is exact (stage C1d)

On an array candidate set whose view satisfies `WitP` (implied by `ClosedP`):

- `suppF_iff`: the support test on signatures (`suppF`) is the support
  condition `SuppP` of `FastSound.lean`;
- `elimW_spec`: the worklist elimination keeps exactly the greatest
  self-supporting set of nodes, so `aliveFast` agrees with `aliveArr` of
  the view (`aliveFast_iff`);
- `fastRowsA_eq`: the array readout equals `fastRows` of the view;
- `fastClassifyA_spec`: the fast checked route is exact, with the
  statement of `fastClassify_spec`.
-/

namespace ContextCalculus.SRIQ.Fast

open ContextCalculus.SRI (RoleT Interp)
open ContextCalculus.SRIQ

variable {n m : Nat}

/-! ## The generic search -/

section DfsG

variable {α κ : Type} (cnt : κ → α → Bool)

/-- `E` meets the needs and stays within the limits. -/
def SolG (E : List α) (needs lims : List (κ × Nat)) : Prop :=
  (∀ x ∈ needs, x.2 ≤ E.countP (cnt x.1)) ∧ (∀ y ∈ lims, E.countP (cnt y.1) ≤ y.2)

variable {cnt}

theorem mem_subG {c : α} {l : List (κ × Nat)} {x : κ × Nat} (hx : x ∈ l) :
    (x.1, if cnt x.1 c then x.2 - 1 else x.2) ∈ subG cnt c l :=
  List.mem_map.2 ⟨x, hx, rfl⟩

theorem dfsG_sound {cs : List α} : ∀ (f : Nat) (needs lims : List (κ × Nat)),
    dfsG cnt cs f needs lims = true → ∃ E, (∀ c ∈ E, c ∈ cs) ∧ SolG cnt E needs lims := by
  intro f
  induction f with
  | zero =>
    intro needs lims h
    rw [dfsG] at h
    split at h
    · next hn =>
      refine ⟨[], by simp, fun x hx => ?_, fun y _ => by simp⟩
      have := List.find?_eq_none.1 hn x hx
      simp only [decide_eq_true_eq, not_lt] at this
      simp [this]
    · simp at h
  | succ f ih =>
    intro needs lims h
    rw [dfsG] at h
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
      · have := hs1 _ (mem_subG (c := c) hx)
        simp only [List.countP_cons]
        split at this <;> simp_all <;> omega
      · have := hs2 _ (mem_subG (c := c) hy)
        simp only [List.countP_cons]
        rcases hlim y hy with h0 | h0
        · simp only [h0, Bool.false_eq_true, ↓reduceIte, add_zero] at this ⊢
          exact this
        · split at this <;> simp_all <;> omega

theorem sum_subG_lt {c : α} : ∀ (l : List (κ × Nat)) (x : κ × Nat), x ∈ l → cnt x.1 c = true →
    0 < x.2 → ((subG cnt c l).map (·.2)).sum < (l.map (·.2)).sum
  | [], _, hx, _, _ => by simp at hx
  | y :: l, x, hx, hc, hpos => by
    have hle : ∀ l : List (κ × Nat), ((subG cnt c l).map (·.2)).sum ≤ (l.map (·.2)).sum := by
      intro l
      induction l with
      | nil => simp [subG]
      | cons z l ih =>
        simp only [subG, List.map_cons, List.sum_cons] at ih ⊢
        split <;> omega
    simp only [subG, List.map_cons, List.sum_cons] at *
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [if_pos hc]
      have := hle l
      simp only [subG] at this
      omega
    · have := sum_subG_lt l x hx hc hpos
      simp only [subG] at this
      split <;> omega

theorem dfsG_complete [DecidableEq α] {cs : List α} : ∀ (f : Nat) (needs lims : List (κ × Nat)) (E : List α),
    (∀ c ∈ E, c ∈ cs) → SolG cnt E needs lims → (needs.map (·.2)).sum < f →
    dfsG cnt cs f needs lims = true := by
  intro f
  induction f with
  | zero => intro _ _ _ _ _ h; omega
  | succ f ih =>
    intro needs lims E hE hS hf
    rw [dfsG]
    split
    · rfl
    · next x hx =>
      have hxm := List.mem_of_find?_eq_some hx
      have hxp : 0 < x.2 := by simpa using List.find?_some hx
      have hcnt := hS.1 x hxm
      obtain ⟨c, hcE, hcx⟩ := List.countP_pos_iff.1 (lt_of_lt_of_le hxp hcnt)
      refine List.any_eq_true.2 ⟨c, hE c hcE, ?_⟩
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_true_eq]
      refine ⟨⟨hcx, fun y hy => ?_⟩, ?_⟩
      · by_cases hy0 : cnt y.1 c = true
        · right
          have h1 := hS.2 y hy
          have h2 : 0 < E.countP (cnt y.1) := List.countP_pos_iff.2 ⟨c, hcE, hy0⟩
          omega
        · left; simpa using hy0
      · refine ih _ _ (E.erase c) (fun c' hc' => hE c' (List.mem_of_mem_erase hc')) ⟨?_, ?_⟩ ?_
        · intro x' hx'
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx'
          have h1 := hS.1 z hz
          rw [List.countP_erase]
          by_cases hzc : cnt z.1 c = true
          · simp only [hcE, hzc, and_self, if_true]; omega
          · simp only [hzc, and_false, if_false, Bool.false_eq_true]; omega
        · intro y' hy'
          obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy'
          have h1 := hS.2 z hz
          rw [List.countP_erase]
          by_cases hzc : cnt z.1 c = true
          · simp only [hcE, hzc, and_self, if_true]; omega
          · simp only [hzc, and_false, if_false, Bool.false_eq_true]; omega
        · have := sum_subG_lt needs x hxm hcx hxp
          omega

end DfsG

/-! ## The search with a memo -/

section DfsMP

variable {α : Type} {cnt : Nat → α → Bool} {cs : List α}

/-- A solution from the entries of `cs`. -/
def HasSol (cnt : Nat → α → Bool) (cs : List α) (needs lims : List (Nat × Nat)) : Prop :=
  ∃ E, (∀ c ∈ E, c ∈ cs) ∧ SolG cnt E needs lims

/-- Every state of the memo has no solution. -/
def MemoOK (cnt : Nat → α → Bool) (cs : List α) (memo : Std.HashSet MSt) : Prop :=
  ∀ st : MSt, memo.contains st = true → ¬ HasSol cnt cs st.1 st.2

theorem memoOK_insert {memo : Std.HashSet MSt} (h : MemoOK cnt cs memo) {st : MSt}
    (hst : ¬ HasSol cnt cs st.1 st.2) : MemoOK cnt cs (memo.insert st) := by
  intro st' hc
  rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with rfl | hc
  · exact hst
  · exact h st' hc

theorem sol_nil {needs lims : List (Nat × Nat)} (hn : needs.find? (fun x => decide (0 < x.2)) = none) :
    SolG cnt [] needs lims := by
  refine ⟨fun x hx => ?_, fun y _ => by simp⟩
  have := List.find?_eq_none.1 hn x hx
  simp only [decide_eq_true_eq, not_lt] at this
  simp [this]

theorem sol_cons {needs lims : List (Nat × Nat)} {c : α} {E : List α}
    (hlim : ∀ y ∈ lims, cnt y.1 c = false ∨ 0 < y.2)
    (h : SolG cnt E (subG cnt c needs) (subG cnt c lims)) : SolG cnt (c :: E) needs lims := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have := h.1 _ (mem_subG (c := c) hx)
    simp only [List.countP_cons]
    split at this <;> simp_all <;> omega
  · have := h.2 _ (mem_subG (c := c) hy)
    simp only [List.countP_cons]
    rcases hlim y hy with h0 | h0
    · simp only [h0, Bool.false_eq_true, ↓reduceIte, add_zero] at this ⊢
      exact this
    · split at this <;> simp_all <;> omega

theorem sol_erase [DecidableEq α] {needs lims : List (Nat × Nat)} {c : α} {E : List α}
    (hS : SolG cnt E needs lims) (hcE : c ∈ E) :
    (∀ y ∈ lims, cnt y.1 c = false ∨ 0 < y.2) ∧ SolG cnt (E.erase c) (subG cnt c needs) (subG cnt c lims) := by
  refine ⟨fun y hy => ?_, ?_, ?_⟩
  · by_cases hy0 : cnt y.1 c = true
    · right
      have h1 := hS.2 y hy
      have h2 : 0 < E.countP (cnt y.1) := List.countP_pos_iff.2 ⟨c, hcE, hy0⟩
      omega
    · left; simpa using hy0
  · intro x' hx'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx'
    have h1 := hS.1 z hz
    rw [List.countP_erase]
    by_cases hzc : cnt z.1 c = true
    · simp only [hcE, hzc, and_self, if_true]; omega
    · simp only [hzc, and_false, if_false, Bool.false_eq_true]; omega
  · intro y' hy'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy'
    have h1 := hS.2 z hz
    rw [List.countP_erase]
    by_cases hzc : cnt z.1 c = true
    · simp only [hcE, hzc, and_self, if_true]; omega
    · simp only [hzc, and_false, if_false, Bool.false_eq_true]; omega

theorem okC_iff {x : Nat × Nat} {lims : List (Nat × Nat)} {c : α} :
    okC cnt x lims c = true ↔ cnt x.1 c = true ∧ ∀ y ∈ lims, cnt y.1 c = false ∨ 0 < y.2 := by
  simp only [okC, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq]

/-- A solution exists iff some entry that counts for the first unmet need
leads to a solution of the rest. -/
theorem hasSol_step [DecidableEq α] {needs lims : List (Nat × Nat)} {x : Nat × Nat}
    (hx : needs.find? (fun x => decide (0 < x.2)) = some x) :
    HasSol cnt cs needs lims ↔
      ∃ c ∈ cs, okC cnt x lims c = true ∧ HasSol cnt cs (subG cnt c needs) (subG cnt c lims) := by
  constructor
  · rintro ⟨E, hE, hS⟩
    have hxm := List.mem_of_find?_eq_some hx
    have hxp : 0 < x.2 := by simpa using List.find?_some hx
    obtain ⟨c, hcE, hcx⟩ := List.countP_pos_iff.1 (lt_of_lt_of_le hxp (hS.1 x hxm))
    obtain ⟨hl, hS'⟩ := sol_erase hS hcE
    exact ⟨c, hE c hcE, okC_iff.2 ⟨hcx, hl⟩,
      ⟨E.erase c, fun c' hc' => hE c' (List.mem_of_mem_erase hc'), hS'⟩⟩
  · rintro ⟨c, hc, hok, E, hE, hS⟩
    refine ⟨c :: E, fun c' hc' => ?_, sol_cons (okC_iff.1 hok).2 hS⟩
    rcases List.mem_cons.1 hc' with rfl | h'
    · exact hc
    · exact hE c' h'

theorem dfsM_spec [DecidableEq α] : ∀ (f : Nat) (needs lims : List (Nat × Nat)) (memo : Std.HashSet MSt),
    MemoOK cnt cs memo → (needs.map (·.2)).sum < f →
      ((dfsM cnt cs f needs lims memo).1 = true ↔ HasSol cnt cs needs lims) ∧
        MemoOK cnt cs (dfsM cnt cs f needs lims memo).2 := by
  intro f
  induction f with
  | zero => intro _ _ _ _ h; omega
  | succ f ih =>
    intro needs lims memo hM hf
    -- the candidates of one need, as a statement on `tryM` by induction on the list
    have hT : ∀ (x : Nat × Nat), needs.find? (fun x => decide (0 < x.2)) = some x →
        ∀ (l : List α) (memo : Std.HashSet MSt), MemoOK cnt cs memo →
          ((tryM cnt cs f x needs lims l memo).1 = true ↔
            ∃ c ∈ l, okC cnt x lims c = true ∧ HasSol cnt cs (subG cnt c needs) (subG cnt c lims)) ∧
          MemoOK cnt cs (tryM cnt cs f x needs lims l memo).2 := by
      intro x hx l
      induction l with
      | nil => intro memo hM; simp [tryM, hM]
      | cons c rest ihl =>
        intro memo hM
        rw [tryM]
        split
        · next hok =>
          have hsub : ((subG cnt c needs).map (·.2)).sum < f := by
            have hxm := List.mem_of_find?_eq_some hx
            have hxp : 0 < x.2 := by simpa using List.find?_some hx
            have := sum_subG_lt needs x hxm (okC_iff.1 hok).1 hxp
            omega
          obtain ⟨h1, h2⟩ := ih (subG cnt c needs) (subG cnt c lims) memo hM hsub
          dsimp only
          split
          · next hr =>
            refine ⟨⟨fun _ => ⟨c, List.mem_cons_self, hok, h1.1 hr⟩, fun _ => hr⟩, h2⟩
          · next hr =>
            obtain ⟨h3, h4⟩ := ihl _ h2
            refine ⟨?_, h4⟩
            rw [h3]
            constructor
            · rintro ⟨c', hc', hok', hs'⟩; exact ⟨c', List.mem_cons_of_mem _ hc', hok', hs'⟩
            · rintro ⟨c', hc', hok', hs'⟩
              rcases List.mem_cons.1 hc' with rfl | hc'
              · exact absurd (h1.2 hs') (by simpa using hr)
              · exact ⟨c', hc', hok', hs'⟩
        · next hok =>
          obtain ⟨h3, h4⟩ := ihl memo hM
          refine ⟨?_, h4⟩
          rw [h3]
          constructor
          · rintro ⟨c', hc', hok', hs'⟩; exact ⟨c', List.mem_cons_of_mem _ hc', hok', hs'⟩
          · rintro ⟨c', hc', hok', hs'⟩
            rcases List.mem_cons.1 hc' with rfl | hc'
            · exact absurd hok' (by simpa using hok)
            · exact ⟨c', hc', hok', hs'⟩
    rw [dfsM]
    split
    · next hn => exact ⟨⟨fun _ => ⟨[], by simp, sol_nil hn⟩, fun _ => rfl⟩, hM⟩
    · next x hx =>
      dsimp only
      split
      · next hc =>
        exact ⟨⟨fun h => absurd h (by simp), fun h => absurd h (hM _ hc)⟩, hM⟩
      · next hc =>
        obtain ⟨h1, h2⟩ := hT x hx cs memo hM
        split
        · next hr => exact ⟨⟨fun _ => (hasSol_step hx).2 (h1.1 hr), fun _ => hr⟩, h2⟩
        · next hr =>
          have hno : ¬ HasSol cnt cs needs lims := fun hs => hr (h1.2 ((hasSol_step hx).1 hs))
          exact ⟨⟨fun h => absurd h (by simp), fun h => absurd h hno⟩, memoOK_insert h2 hno⟩

/-- **The memo search decides the search problem.** -/
theorem dfsM_iff [DecidableEq α] {needs lims : List (Nat × Nat)} :
    (dfsM cnt cs ((needs.map (·.2)).sum + 1) needs lims ∅).1 = true ↔ HasSol cnt cs needs lims :=
  (dfsM_spec _ needs lims ∅ (fun st h => by simp at h) (Nat.lt_succ_self _)).1

end DfsMP

/-! ## Signatures -/

section Sig

theorem cntS_sigTwo {L : List ((RoleT (Fin m) × Fin n) × Nat)} {lab ty : Array Nat} (p : Nat) :
    cntS p (sigTwo ((L.zipIdx).filter fun z => bsA lab (rc z.1.1.1)) ty) = true ↔
      ∃ x, L[p]? = some x ∧ cntA x.1 (lab, ty) = true := by
  simp only [cntS, sigTwo, Array.contains_iff_mem, List.mem_toArray, List.mem_map, List.mem_filter,
    List.mem_zipIdx_iff_getElem?, cntA, Bool.and_eq_true]
  constructor
  · rintro ⟨z, ⟨⟨hz, h1⟩, h2⟩, rfl⟩
    exact ⟨z.1, hz, h1, h2⟩
  · rintro ⟨x, hx, h1, h2⟩
    exact ⟨(x, p), ⟨⟨hx, h1⟩, h2⟩, rfl⟩

/-- A signature and an entry that agree on every position of `L`. -/
def SigRel (L : List ((RoleT (Fin m) × Fin n) × Nat)) (s : Array Nat) (c : Array Nat × Array Nat) : Prop :=
  ∀ p, cntS p s = true ↔ ∃ x, L[p]? = some x ∧ cntA x.1 c = true

theorem countP_sigRel {L : List ((RoleT (Fin m) × Fin n) × Nat)} :
    ∀ {Es : List (Array Nat)} {Ec : List (Array Nat × Array Nat)}, List.Forall₂ (SigRel L) Es Ec →
    ∀ {p : Nat} {x : (RoleT (Fin m) × Fin n) × Nat}, L[p]? = some x →
      Es.countP (cntS p) = Ec.countP (cntA x.1)
  | [], [], .nil, _, _, _ => rfl
  | s :: Es, c :: Ec, .cons hsc h, p, x, hx => by
    rw [List.countP_cons, List.countP_cons, countP_sigRel h hx]
    have : cntS p s = cntA x.1 c := by
      rw [Bool.eq_iff_iff, hsc p]
      constructor
      · rintro ⟨y, hy, hc⟩; rw [hx] at hy; cases hy; exact hc
      · intro hc; exact ⟨x, hx, hc⟩
    rw [this]

theorem solG_sigRel {needs lims : List ((RoleT (Fin m) × Fin n) × Nat)} {Es : List (Array Nat)}
    {Ec : List (Array Nat × Array Nat)} (h : List.Forall₂ (SigRel (needs ++ lims)) Es Ec) :
    SolG cntS Es (needs.zipIdx.map fun p => (p.2, p.1.2))
        (lims.zipIdx.map fun p => (needs.length + p.2, p.1.2)) ↔
      SolG cntA Ec needs lims := by
  have hn : ∀ {p : Nat} {y}, needs[p]? = some y → (needs ++ lims)[p]? = some y := by
    intro p y hy
    have hp : p < needs.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hy; simp at hy
    rw [List.getElem?_append_left hp]; exact hy
  have hl : ∀ {p : Nat} {y}, lims[p]? = some y → (needs ++ lims)[needs.length + p]? = some y := by
    intro p y hy
    rw [List.getElem?_append_right (by omega)]; simpa using hy
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hx
      have := h1 (p, x.2) (List.mem_map.2 ⟨(x, p), List.mem_zipIdx_iff_getElem?.2 hp, rfl⟩)
      rwa [countP_sigRel h (hn hp)] at this
    · obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hy
      have := h2 (needs.length + p, y.2) (List.mem_map.2 ⟨(y, p), List.mem_zipIdx_iff_getElem?.2 hp, rfl⟩)
      rwa [countP_sigRel h (hl hp)] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · obtain ⟨⟨x, p⟩, hxp, rfl⟩ := List.mem_map.1 hz
      rw [List.mem_zipIdx_iff_getElem?] at hxp
      show x.2 ≤ _
      rw [countP_sigRel h (hn hxp)]
      exact h1 x (List.mem_of_getElem? hxp)
    · obtain ⟨⟨y, p⟩, hyp, rfl⟩ := List.mem_map.1 hz
      rw [List.mem_zipIdx_iff_getElem?] at hyp
      show _ ≤ y.2
      rw [countP_sigRel h (hl hyp)]
      exact h2 y (List.mem_of_getElem? hyp)

end Sig

/-! ## The support test -/

section Support

variable {O : Ontology (Fin n) (Fin m)} {C : CandA} {req : List (Fin n)}

theorem forall₂_of_exists {α β : Type} {R : α → β → Prop} :
    ∀ l : List α, (∀ a ∈ l, ∃ b, R a b) → ∃ l' : List β, List.Forall₂ R l l'
  | [], _ => ⟨[], .nil⟩
  | a :: l, h => by
    obtain ⟨b, hb⟩ := h a List.mem_cons_self
    obtain ⟨l', hl'⟩ := forall₂_of_exists l fun a' ha' => h a' (List.mem_cons_of_mem _ ha')
    exact ⟨b :: l', .cons hb hl'⟩

theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | [], [], .nil, _, hb => by simp at hb
  | a :: l, b' :: l', .cons hab h, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hab⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem_right h b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem forall₂_mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ a ∈ l, ∃ b ∈ l', R a b
  | [], [], .nil, _, ha => by simp at ha
  | a' :: l, b :: l', .cons hab h, a, ha => by
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, List.mem_cons_self, hab⟩
    · obtain ⟨b', hb', h'⟩ := forall₂_mem_left h a ha
      exact ⟨b', List.mem_cons_of_mem _ hb', h'⟩

theorem forall₂_imp {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → List.Forall₂ S l l'
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hab h => .cons (hRS _ _ hab) (forall₂_imp hRS h)

theorem countP_forall₂ {α β : Type} {p : α → Bool} {q : β → Bool} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ (fun a b => p a = q b) l l' → l.countP p = l'.countP q
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons hab h => by rw [List.countP_cons, List.countP_cons, hab, countP_forall₂ h]

theorem forall₂_map_fst_snd {α β : Type} {R : α → β → Prop} :
    ∀ {L : List (α × β)}, (∀ x ∈ L, R x.1 x.2) → List.Forall₂ R (L.map (·.1)) (L.map (·.2))
  | [], _ => .nil
  | x :: L, h => .cons (h x List.mem_cons_self) (forall₂_map_fst_snd fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem forall₂_map_snd {α β γ : Type} {R : α → γ → Prop} :
    ∀ {l : List α} {L : List (β × γ)}, List.Forall₂ (fun a x => R a x.2) l L → List.Forall₂ R l (L.map (·.2))
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons h hs => .cons h (forall₂_map_snd hs)

theorem cntA_view {lab ty : Array Nat} (hl : SortedA lab) (ht : SortedA ty) (x : RoleT (Fin m) × Fin n) :
    cntA x (lab, ty) = cntP x.1 x.2 (absLab m lab, absTy n ty) := by
  symm
  refine decide_eq_of_iff ?_
  simp only [cntA, Bool.and_eq_true, bsA_iff hl, bsA_iff ht, mem_absLab, mem_absTy]

/-- The entries of the per-node data are pool entries and child nodes, with
their signatures. -/
theorem cands_sound {i : Nat} {p : Nat × (Array Nat × Array Nat) × Array Nat}
    (hp : p ∈ (mkNodeE (mkIx O) C i).cands) :
    ∃ e ∈ (ndA C i).pool, p.1 ∈ membA C e.kid ∧ (bkA C p.1).all (bsA (ndA C i).ty) = true ∧
      p.2.1 = (e.lab, (ndA C p.1).ty) ∧
      SigRel ((mkNodeE (mkIx O) C i).needs ++ (mkNodeE (mkIx O) C i).lims) p.2.2 p.2.1 := by
  simp only [mkNodeE, List.mem_flatMap] at hp
  obtain ⟨e, he, hp⟩ := hp
  split at hp
  · obtain ⟨j, hj, hp⟩ := List.mem_filterMap.1 hp
    split at hp
    · simp only [Option.some.injEq] at hp
      subst hp
      obtain ⟨hj, hb⟩ := List.mem_filter.1 hj
      exact ⟨e, he, hj, hb, rfl, fun p => cntS_sigTwo p⟩
    · simp at hp
  · simp at hp

theorem cands_complete {i : Nat} {e : EntryA} (he : e ∈ (ndA C i).pool) {j : Nat}
    (hj : j ∈ membA C e.kid) (hb : (bkA C j).all (bsA (ndA C i).ty) = true)
    (hs : ∃ x ∈ (mkNodeE (mkIx O) C i).needs, cntA x.1 (e.lab, (ndA C j).ty) = true) :
    ∃ s, (j, (e.lab, (ndA C j).ty), s) ∈ (mkNodeE (mkIx O) C i).cands ∧
      SigRel ((mkNodeE (mkIx O) C i).needs ++ (mkNodeE (mkIx O) C i).lims) s (e.lab, (ndA C j).ty) := by
  obtain ⟨x, hx, hc⟩ := hs
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hx
  have hpl : p < (mkNodeE (mkIx O) C i).needs.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hp; simp at hp
  have hpa : ((mkNodeE (mkIx O) C i).needs ++ (mkNodeE (mkIx O) C i).lims)[p]? = some x := by
    rw [List.getElem?_append_left hpl]; exact hp
  refine ⟨_, ?_, fun p => cntS_sigTwo p⟩
  simp only [mkNodeE] at hpa hpl ⊢
  refine List.mem_flatMap.2 ⟨e, he, ?_⟩
  have hlab : bsA e.lab (rc x.1.1) = true := by simp only [cntA, Bool.and_eq_true] at hc; exact hc.1
  rw [if_pos]
  · refine List.mem_filterMap.2 ⟨j, List.mem_filter.2 ⟨hj, hb⟩, ?_⟩
    rw [if_pos]
    rw [Array.any_eq_true]
    have hin := (cntS_sigTwo (L := _) (lab := e.lab) (ty := (ndA C j).ty) p).2 ⟨x, hpa, hc⟩
    simp only [cntS, Array.contains_iff_mem] at hin
    obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.1 hin
    exact ⟨k, hk, by rw [hke]; simpa using hpl⟩
  · rw [List.any_eq_true]
    exact ⟨(x, p), List.mem_filter.2 ⟨List.mem_zipIdx_iff_getElem?.2 hpa, hlab⟩, by simpa using hpl⟩

theorem mem_needsE {i : Nat} {x : (RoleT (Fin m) × Fin n) × Nat} (hx : x ∈ (mkNodeE (mkIx O) C i).needs) :
    ∃ q ∈ lowAtA (mkIx O) (ndA C i).ty, x = ((q.2.2.1, q.2.2.2),
      q.2.1 - pcBA (keyA C (ndA C i).ctx) q.2.2.1 q.2.2.2) ∧ 0 < x.2 := by
  simp only [mkNodeE, List.mem_filter, List.mem_map, decide_eq_true_eq] at hx
  obtain ⟨⟨q, hq, rfl⟩, hpos⟩ := hx
  exact ⟨q, hq, rfl, hpos⟩

theorem needsE_mem {i : Nat} {q : Fin n × Nat × RoleT (Fin m) × Fin n} (hq : q ∈ lowAtA (mkIx O) (ndA C i).ty)
    (hpos : 0 < q.2.1 - pcBA (keyA C (ndA C i).ctx) q.2.2.1 q.2.2.2) :
    ((q.2.2.1, q.2.2.2), q.2.1 - pcBA (keyA C (ndA C i).ctx) q.2.2.1 q.2.2.2) ∈
      (mkNodeE (mkIx O) C i).needs := by
  simp only [mkNodeE, List.mem_filter, List.mem_map, decide_eq_true_eq]
  exact ⟨⟨q, hq, rfl⟩, hpos⟩

theorem limsE_mem {i : Nat} {u : Fin n × Nat × RoleT (Fin m) × Fin n} (hu : u ∈ uppAtA (mkIx O) (ndA C i).ty) :
    ((u.2.2.1, u.2.2.2), u.2.1 - pcBA (keyA C (ndA C i).ctx) u.2.2.1 u.2.2.2) ∈
      (mkNodeE (mkIx O) C i).lims := by
  simp only [mkNodeE, List.mem_map]
  exact ⟨u, hu, rfl⟩

theorem nS_eq (i : Nat) : (mkNodeE (mkIx O) C i).nS =
    (mkNodeE (mkIx O) C i).needs.zipIdx.map fun p => (p.2, p.1.2) := rfl

theorem lS_eq (i : Nat) : (mkNodeE (mkIx O) C i).lS =
    (mkNodeE (mkIx O) C i).lims.zipIdx.map fun p => ((mkNodeE (mkIx O) C i).needs.length + p.2, p.1.2) := rfl

theorem limOK_iff (hW : WF n m C) (i : Nat) :
    (mkNodeE (mkIx O) C i).limOK = true ↔ limsOK (mkIx O) (C.view n m) i := by
  simp only [mkNodeE, List.all_eq_true, decide_eq_true_eq, limsOK, view_nd_ty, view_key_ctx,
    ← uppAtA_eq _ (hW.ty i), pcBA_eq (hW.lab _) (hW.pi _)]

/-- The node, entry and back-set parts of the closure conditions: all that
the worklist elimination needs (`aliveFast_iff`). A candidate set that is
only a witness for the live types (stage C1f) satisfies these without the
rules R1 to R6. -/
def WitP (ix : Ix n m) (U : Cand n m) : Prop :=
  (∀ i < U.nodes.size, nodeOK ix U i ∧ (∀ e ∈ (nd U i).pool, entryOK ix U (nd U i).ty e) ∧ True) ∧
  ∀ j < U.nodes.size, bkOf U j = backOf ix U j

theorem ClosedP.witP {ix : Ix n m} {U : Cand n m} {req : List (Fin n)} (h : ClosedP ix U req) :
    WitP ix U :=
  ⟨fun i hi => ⟨(h.2.2.2.1 i hi).1, (h.2.2.2.1 i hi).2.1, trivial⟩, h.2.2.2.2.1⟩

theorem bk_sub_iff (hC : WitP (mkIx O) (C.view n m)) (hW : WF n m C) {i j : Nat}
    (hj : j < C.nodes.size) :
    (bkA C j).all (bsA (ndA C i).ty) = true ↔ backOf (mkIx O) (C.view n m) j ⊆ (nd (C.view n m) i).ty := by
  rw [← hC.2 j (by simpa using hj), bkOf_view, view_nd_ty]
  constructor
  · intro h y hy
    rw [mem_absTy] at hy ⊢
    exact bsA_sound (all_mem h hy)
  · intro h
    rw [← Array.all_toList, List.all_eq_true]
    intro x hx
    have := h ((mem_absTy (y := ⟨x, hW.bkB j x (Array.mem_def.2 hx)⟩)).2 (Array.mem_def.2 hx))
    exact (bsA_iff (hW.ty i)).2 (mem_absTy.1 this)

/-- **The support test on signatures is exact.** -/
theorem suppF_iff (hC : WitP (mkIx O) (C.view n m)) (hW : WF n m C) {i : Nat}
    (hi : i < C.nodes.size) (A : Array Bool) :
    suppF (mkNodeE (mkIx O) C i) A = true ↔ SuppP O (C.view n m) (fun j => A[j]? = some true) i := by
  have hNC := hC.1 i (by simpa using hi)
  set E := mkNodeE (mkIx O) C i with hE
  set ss := dedupKey id ((E.cands.filter fun p => A[p.1]?.getD false).map (·.2.2)) with hss
  have hcount : ∀ c : Array Nat × Array Nat, (∃ e ∈ (ndA C i).pool, ∃ j, c = (e.lab, (ndA C j).ty)) →
      ∀ x : RoleT (Fin m) × Fin n, cntA x c = cntP x.1 x.2 (absLab m c.1, absTy n c.2) := by
    rintro c ⟨e, he, j, rfl⟩ x
    exact cntA_view (hW.ent i e he).1 (hW.ty j) x
  constructor
  · intro h
    simp only [suppF, ← hss, Bool.and_eq_true] at h
    obtain ⟨⟨hlim, -⟩, hd⟩ := h
    obtain ⟨Es, hEs, hsol⟩ := dfsM_iff.1 hd
    have hlive : ∀ s ∈ Es, ∃ p ∈ E.cands, A[p.1]?.getD false = true ∧ p.2.2 = s := by
      intro s hs
      have := dedupKey_subset id _ s (hEs s hs)
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 this
      obtain ⟨hp, hA⟩ := List.mem_filter.1 hp
      exact ⟨p, hp, hA, rfl⟩
    obtain ⟨Ec, hEc⟩ := forall₂_of_exists (R := fun s c => ∃ p ∈ E.cands,
      A[p.1]?.getD false = true ∧ p.2.2 = s ∧ p.2.1 = c) Es fun s hs => by
        obtain ⟨p, hp, hA, hps⟩ := hlive s hs
        exact ⟨p.2.1, p, hp, hA, hps, rfl⟩
    have hrel : List.Forall₂ (SigRel (E.needs ++ E.lims)) Es Ec := forall₂_imp (fun s c => by
      rintro ⟨p, hp, -, rfl, rfl⟩
      obtain ⟨-, -, -, -, -, h⟩ := cands_sound hp
      exact h) hEc
    rw [nS_eq, lS_eq, solG_sigRel hrel] at hsol
    have hEcP : ∀ c ∈ Ec, ∃ p ∈ E.cands, A[p.1]?.getD false = true ∧ p.2.1 = c := by
      intro c hc
      obtain ⟨s, -, p, hp, hA, -, rfl⟩ := forall₂_mem_right hEc c hc
      exact ⟨p, hp, hA, rfl⟩
    have hcnt : ∀ x : RoleT (Fin m) × Fin n,
        (Ec.map fun c => (absLab m c.1, absTy n c.2)).countP (cntP x.1 x.2) = Ec.countP (cntA x) := by
      intro x
      rw [List.countP_map]
      refine List.countP_congr fun c hc => ?_
      obtain ⟨p, hp, -, rfl⟩ := hEcP c hc
      obtain ⟨e, he, -, -, h2, -⟩ := cands_sound hp
      rw [Function.comp_apply, hcount p.2.1 ⟨e, he, p.1, h2⟩ x]
    refine ⟨hNC.1, (limOK_iff hW i).1 hlim, Ec.map fun c => (absLab m c.1, absTy n c.2),
      fun c' hc' => ?_, fun q hq => ?_, fun u hu => ?_⟩
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hc'
      obtain ⟨p, hp, hA, rfl⟩ := hEcP c hc
      obtain ⟨e, he, hj, hb, h2, -⟩ := cands_sound hp
      obtain ⟨hjn, -⟩ := mem_membA hj
      refine ⟨viewEntry n m e, by rw [view_nd_pool]; exact List.mem_map.2 ⟨e, he, rfl⟩,
        hNC.2.1 _ (by rw [view_nd_pool]; exact List.mem_map.2 ⟨e, he, rfl⟩), p.1,
        by rw [memb_view]; exact hj, ?_, (bk_sub_iff hC hW hjn).1 hb, ?_⟩
      · show A[p.1]? = some true
        revert hA; cases A[p.1]? <;> simp
      · rw [h2, view_nd_ty]; rfl
    · rw [view_nd_ty, ← lowAtA_eq _ (hW.ty i)] at hq
      rw [view_key_ctx, ← pcBA_eq (hW.lab _) (hW.pi _)]
      have := hcnt (q.2.2.1, q.2.2.2)
      simp only at this
      rw [this]
      by_cases hpos : 0 < q.2.1 - pcBA (keyA C (ndA C i).ctx) q.2.2.1 q.2.2.2
      · have := hsol.1 _ (needsE_mem hq hpos)
        simp only at this
        omega
      · omega
    · rw [view_nd_ty, ← uppAtA_eq _ (hW.ty i)] at hu
      rw [view_key_ctx, ← pcBA_eq (hW.lab _) (hW.pi _)]
      have := hcnt (u.2.2.1, u.2.2.2)
      simp only at this
      rw [this]
      have h1 := hsol.2 _ (limsE_mem hu)
      have h2 : pcBA (keyA C (ndA C i).ctx) u.2.2.1 u.2.2.2 ≤ u.2.1 := by
        simp only [hE, mkNodeE, List.all_eq_true, decide_eq_true_eq] at hlim
        exact hlim u hu
      simp only at h1
      omega
  · rintro ⟨-, hlo, EF, hcand, hlow, hupp⟩
    -- the entries that serve a need
    set E1 := EF.filter fun c => E.needs.any fun x => cntP x.1.1 x.1.2 c with hE1
    have hpick : ∀ c ∈ E1, ∃ sc : Array Nat × (Array Nat × Array Nat), sc.1 ∈ ss ∧
        SigRel (E.needs ++ E.lims) sc.1 sc.2 ∧ (absLab m sc.2.1, absTy n sc.2.2) = c ∧
        ∃ e ∈ (ndA C i).pool, ∃ j, sc.2 = (e.lab, (ndA C j).ty) := by
      intro c hc
      obtain ⟨hcF, hserve⟩ := List.mem_filter.1 hc
      obtain ⟨e', he', -, j, hj, hA, hb, rfl⟩ := hcand c hcF
      rw [view_nd_pool] at he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
      rw [memb_view] at hj
      obtain ⟨hjn, -⟩ := mem_membA hj
      have hcA : ∀ x : RoleT (Fin m) × Fin n, cntA x (e.lab, (ndA C j).ty) =
          cntP x.1 x.2 ((viewEntry n m e).spec.lab, (nd (C.view n m) j).ty) := by
        intro x; rw [view_nd_ty]; exact cntA_view (hW.ent i e he).1 (hW.ty j) x
      obtain ⟨x, hx, hxc⟩ := List.any_eq_true.1 hserve
      obtain ⟨sg, hsg, hrel⟩ := cands_complete he hj ((bk_sub_iff hC hW hjn).2 hb)
        ⟨x, hx, by rw [hcA]; exact hxc⟩
      have hlv : sg ∈ (E.cands.filter fun p => A[p.1]?.getD false).map (·.2.2) :=
        List.mem_map.2 ⟨_, List.mem_filter.2 ⟨hsg, by simp [hA]⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := exists_dedupKey id _ sg hlv
      simp only [id] at hyx
      subst hyx
      exact ⟨(y, (e.lab, (ndA C j).ty)), hy, hrel, by rw [view_nd_ty]; rfl, e, he, j, rfl⟩
    obtain ⟨L, hL⟩ := forall₂_of_exists _ hpick
    have hLmem : ∀ sc ∈ L, sc.1 ∈ ss ∧ SigRel (E.needs ++ E.lims) sc.1 sc.2 ∧
        ∃ e ∈ (ndA C i).pool, ∃ j, sc.2 = (e.lab, (ndA C j).ty) := by
      intro sc hsc
      obtain ⟨c, -, h1, h2, -, h4⟩ := forall₂_mem_right hL sc hsc
      exact ⟨h1, h2, h4⟩
    have hrel : List.Forall₂ (SigRel (E.needs ++ E.lims)) (L.map (·.1)) (L.map (·.2)) :=
      forall₂_map_fst_snd fun sc hsc => (hLmem sc hsc).2.1
    have hcnt : ∀ x : RoleT (Fin m) × Fin n, (L.map (·.2)).countP (cntA x) = E1.countP (cntP x.1 x.2) := by
      intro x
      symm
      refine countP_forall₂ (forall₂_map_snd (forall₂_imp (fun c sc h => ?_) hL))
      obtain ⟨-, -, h3, h4⟩ := h
      rw [← h3, hcount sc.2 h4 x]
    have hsolA : SolG cntA (L.map (·.2)) E.needs E.lims := by
      refine ⟨fun x hx => ?_, fun y hy => ?_⟩
      · obtain ⟨q, hq, rfl, hpos⟩ := mem_needsE hx
        rw [hcnt]
        have h1 := hlow q (by rw [view_nd_ty, ← lowAtA_eq _ (hW.ty i)]; exact hq)
        rw [view_key_ctx, ← pcBA_eq (hW.lab _) (hW.pi _)] at h1
        have h2 : E1.countP (cntP q.2.2.1 q.2.2.2) = EF.countP (cntP q.2.2.1 q.2.2.2) := by
          rw [hE1, List.countP_filter]
          refine List.countP_congr fun c _ => ?_
          constructor
          · intro h; exact (Bool.and_eq_true _ _ ▸ h).1
          · intro h
            refine Bool.and_eq_true _ _ ▸ ⟨h, List.any_eq_true.2 ⟨_, hx, h⟩⟩
        simp only at h2 ⊢
        omega
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (by simpa only [hE, mkNodeE] using hy)
        rw [hcnt]
        have h1 := hupp u (by rw [view_nd_ty, ← uppAtA_eq _ (hW.ty i)]; exact hu)
        rw [view_key_ctx, ← pcBA_eq (hW.lab _) (hW.pi _)] at h1
        have h2 : E1.countP (cntP u.2.2.1 u.2.2.2) ≤ EF.countP (cntP u.2.2.1 u.2.2.2) :=
          (List.filter_sublist).countP_le
        simp only
        omega
    have hsolS := (solG_sigRel hrel).2 hsolA
    rw [← nS_eq, ← lS_eq] at hsolS
    simp only [suppF, ← hss, Bool.and_eq_true, List.all_eq_true, List.any_eq_true]
    refine ⟨⟨(limOK_iff hW i).2 hlo, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨⟨y, p⟩, hyp, rfl⟩ := List.mem_map.1 (by rw [nS_eq] at hx; exact hx)
      have hy := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hyp)
      obtain ⟨-, -, -, hpos⟩ := mem_needsE hy
      have h1 := hsolS.1 _ (by rw [nS_eq]; exact List.mem_map.2 ⟨(y, p), hyp, rfl⟩)
      simp only at h1
      obtain ⟨s, hs, hsc⟩ := List.countP_pos_iff.1 (lt_of_lt_of_le hpos h1)
      obtain ⟨sc, hsc', rfl⟩ := List.mem_map.1 hs
      exact ⟨sc.1, (hLmem sc hsc').1, hsc⟩
    · refine dfsM_iff.2 ⟨L.map (·.1), fun s hs => ?_, hsolS⟩
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.1 hs
      exact (hLmem sc hsc).1

end Support

/-! ## The worklist -/

section Worklist

variable {O : Ontology (Fin n) (Fin m)} {C : CandA} {req : List (Fin n)}

/-- The live flag as a predicate. -/
def AP (A : Array Bool) (j : Nat) : Prop := A[j]? = some true

theorem ap_iff {A : Array Bool} {j : Nat} : AP A j ↔ A[j]?.getD false = true := by
  unfold AP; cases A[j]? <;> simp

theorem ap_set {A : Array Bool} {i j : Nat} : AP (A.set! i false) j ↔ j ≠ i ∧ AP A j := by
  unfold AP
  rw [Array.set!, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hlt : i < A.size
    · simp [hlt]
    · simp only [hlt, and_false, if_false, ne_eq, not_true_eq_false, false_and, iff_false]
      rw [Array.getElem?_eq_none (by omega)]; simp
  · simp only [hij, false_and, if_false]
    exact ⟨fun h => ⟨fun h' => hij h'.symm, h⟩, fun h => h.2⟩

theorem foldl_set_true : ∀ (ps : List Nat) (Q : Array Bool) (j : Nat),
    (ps.foldl (fun Q μ => Q.set! μ true) Q)[j]? = some true → j ∈ ps ∨ Q[j]? = some true
  | [], Q, j, h => Or.inr h
  | μ :: ps, Q, j, h => by
    rw [List.foldl_cons] at h
    rcases foldl_set_true ps _ j h with h | h
    · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [Array.set!, Array.getElem?_setIfInBounds] at h
      split at h
      · next h' => exact Or.inl (h' ▸ List.mem_cons_self)
      · exact Or.inr h

theorem es_get (i : Nat) (hi : i < C.nodes.size) :
    (nodeEs (mkIx O) C)[i]?.getD default = mkNodeE (mkIx O) C i := by
  simp [nodeEs, hi]

theorem mem_parentsOf (hC : WitP (mkIx O) (C.view n m)) {j : Nat} (hj : j < C.nodes.size)
    {e : EntryA} (he : e ∈ (ndA C j).pool) : j ∈ getL (parentsOf C) e.kid := by
  have hNC := hC.1 j (by simpa using hj)
  have hk : e.kid < C.keys.size := by
    have := (hNC.2.1 (viewEntry n m e) (by rw [view_nd_pool]; exact List.mem_map.2 ⟨e, he, rfl⟩)).1
    simpa [viewEntry] using this
  rw [parentsOf, mem_buildIdx hk]
  exact ⟨(e.kid, j), List.mem_flatMap.2 ⟨j, List.mem_range.2 hj, List.mem_map.2 ⟨e, he, rfl⟩⟩, rfl⟩

/-- A node whose context is no child context of `j` does not support `j`. -/
theorem supp_drop (hC : WitP (mkIx O) (C.view n m)) {A : Array Bool} {i j : Nat}
    (hs : SuppP O (C.view n m) (AP A) j) (hnot : j ∉ getL (parentsOf C) (ndA C i).ctx) :
    SuppP O (C.view n m) (AP (A.set! i false)) j := by
  obtain ⟨h1, h2, E, hE, h3, h4⟩ := hs
  refine ⟨h1, h2, E, fun c hc => ?_, h3, h4⟩
  obtain ⟨e, he, hok, j', hj', hA, hb, rfl⟩ := hE c hc
  refine ⟨e, he, hok, j', hj', ap_set.2 ⟨fun hji => hnot ?_, hA⟩, hb, rfl⟩
  subst hji
  rw [view_nd_pool] at he
  obtain ⟨eA, heA, rfl⟩ := List.mem_map.1 he
  rw [memb_view] at hj'
  obtain ⟨-, hc'⟩ := mem_membA hj'
  have hjn : j < C.nodes.size := by simpa using h1.1
  rw [hc']
  exact mem_parentsOf hC hjn heA

structure WInv (O : Ontology (Fin n) (Fin m)) (C : CandA) (A Q : Array Bool) (q nxt : List Nat) : Prop where
  size : A.size = C.nodes.size
  supp : ∀ j, AP A j → j ∈ q ∨ j ∈ nxt ∨ SuppP O (C.view n m) (AP A) j
  queued : ∀ j, Q[j]? = some true → j ∈ q ∨ j ∈ nxt
  great : ∀ S : Nat → Prop, (∀ j, S j → nodeOK (mkIx O) (C.view n m) j) →
    (∀ j, S j → SuppP O (C.view n m) S j) → ∀ j, S j → AP A j

theorem ap_lt {A : Array Bool} {j : Nat} (h : AP A j) : j < A.size := by
  unfold AP at h
  by_contra hc; rw [Array.getElem?_eq_none (by omega)] at h; simp at h

theorem elimW_spec (hC : WitP (mkIx O) (C.view n m)) (hW : WF n m C) :
    ∀ (A Q : Array Bool) (q nxt : List Nat), WInv O C A Q q nxt →
      (∀ j, AP (elimW C (nodeEs (mkIx O) C) (parentsOf C) A Q q nxt) j →
        SuppP O (C.view n m) (AP (elimW C (nodeEs (mkIx O) C) (parentsOf C) A Q q nxt)) j) ∧
      ∀ S : Nat → Prop, (∀ j, S j → nodeOK (mkIx O) (C.view n m) j) →
        (∀ j, S j → SuppP O (C.view n m) S j) → ∀ j, S j →
          AP (elimW C (nodeEs (mkIx O) C) (parentsOf C) A Q q nxt) j
  | A, Q, [], [], hI => by
    rw [elimW]
    refine ⟨fun j hj => ?_, hI.great⟩
    rcases hI.supp j hj with h | h | h
    · simp at h
    · simp at h
    · exact h
  | A, Q, [], j :: nxt, hI => by
    rw [elimW]
    refine elimW_spec hC hW A Q (j :: nxt) [] ⟨hI.size, fun j' hj' => ?_, fun j' hj' => ?_, hI.great⟩
    · rcases hI.supp j' hj' with h | h | h
      · simp at h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases hI.queued j' hj' with h | h
      · simp at h
      · exact Or.inl h
  | A, Q, i :: q, nxt, hI => by
    rw [elimW]
    dsimp only
    split
    · next h =>
      have hi : i < C.nodes.size := hI.size ▸ ap_lt (ap_iff.2 h.1)
      have hns : ¬ SuppP O (C.view n m) (AP A) i := by
        intro hs
        have := (suppF_iff hC hW hi A).2 hs
        rw [es_get i hi] at h
        rw [h.2] at this
        exact Bool.noConfusion this
      refine elimW_spec hC hW _ _ q _ ⟨by simp [hI.size], fun j hj => ?_, fun j hj => ?_,
        fun S hS hsup j hj => ?_⟩
      · obtain ⟨hji, hj⟩ := ap_set.1 hj
        rcases hI.supp j hj with h' | h' | h'
        · rcases List.mem_cons.1 h' with h' | h'
          · exact absurd h' hji
          · exact Or.inl h'
        · exact Or.inr (Or.inl (List.mem_append_right _ h'))
        · by_cases hjP : j ∈ getL (parentsOf C) (ndA C i).ctx
          · by_cases hq : (Q.set! i false)[j]?.getD false = true
            · have hQ : Q[j]? = some true := by
                rw [Array.set!, Array.getElem?_setIfInBounds, if_neg (Ne.symm hji)] at hq
                exact ap_iff.2 hq
              rcases hI.queued j hQ with h'' | h''
              · rcases List.mem_cons.1 h'' with h'' | h''
                · exact absurd h'' hji
                · exact Or.inl h''
              · exact Or.inr (Or.inl (List.mem_append_right _ h''))
            · refine Or.inr (Or.inl (List.mem_append_left _ (List.mem_filter.2 ⟨hjP, ?_⟩)))
              simp only [Bool.and_eq_true, Bool.not_eq_true']
              exact ⟨ap_iff.1 hj, by simpa using hq⟩
          · exact Or.inr (Or.inr (supp_drop hC h' hjP))
      · rcases foldl_set_true _ _ j hj with h' | h'
        · exact Or.inr (List.mem_append_left _ h')
        · rw [Array.set!, Array.getElem?_setIfInBounds] at h'
          split at h'
          · simp at h'
          · next hij =>
            rcases hI.queued j h' with h'' | h''
            · rcases List.mem_cons.1 h'' with h'' | h''
              · exact absurd h''.symm hij
              · exact Or.inl h''
            · exact Or.inr (List.mem_append_right _ h'')
      · refine ap_set.2 ⟨fun hji => ?_, hI.great S hS hsup j hj⟩
        subst hji
        exact hns (suppP_mono (fun k hk => hI.great S hS hsup k hk) (hsup j hj))
    · next h =>
      refine elimW_spec hC hW _ _ q _ ⟨hI.size, fun j hj => ?_, fun j hj => ?_, hI.great⟩
      · by_cases hji : j = i
        · subst hji
          have hi : j < C.nodes.size := hI.size ▸ ap_lt hj
          refine Or.inr (Or.inr ((suppF_iff hC hW hi A).1 ?_))
          rw [← es_get j hi]
          by_contra hc
          exact h ⟨ap_iff.1 hj, by simpa using hc⟩
        · rcases hI.supp j hj with h' | h' | h'
          · rcases List.mem_cons.1 h' with h' | h'
            · exact absurd h' hji
            · exact Or.inl h'
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
      · rw [Array.set!, Array.getElem?_setIfInBounds] at hj
        split at hj
        · simp at hj
        · next hij =>
          rcases hI.queued j hj with h'' | h''
          · rcases List.mem_cons.1 h'' with h'' | h''
            · exact absurd h''.symm hij
            · exact Or.inl h''
          · exact Or.inr h''
termination_by A _ q nxt => (trues A, 2 * nxt.length + q.length)
decreasing_by
  all_goals first
    | exact Prod.Lex.right _ (by simp)
    | exact Prod.Lex.left _ _ (trues_set_lt (by assumption))
    | (apply Prod.Lex.left; apply trues_set_lt; simp_all)

/-- **The worklist elimination keeps exactly the live nodes of the view.** -/
theorem aliveFast_iff (hC : WitP (mkIx O) (C.view n m)) (hW : WF n m C) (i : Nat) :
    (aliveFast (mkIx O) C)[i]? = some true ↔ Al O (C.view n m) i := by
  have hinit : WInv O C (Array.replicate C.nodes.size true) (Array.replicate C.nodes.size true)
      (List.range C.nodes.size).reverse [] := by
    refine ⟨by simp, fun j hj => ?_, fun j hj => ?_, fun S hS _ j hj => ?_⟩
    · have := ap_lt hj; simp at this
      exact Or.inl (by simp [this])
    · have := ap_lt hj; simp at this
      exact Or.inl (by simp [this])
    · have := (hS j hj).1
      simp only [view_nodes_size] at this
      simp [AP, this]
  obtain ⟨h1, h2⟩ := elimW_spec hC hW _ _ _ _ hinit
  constructor
  · intro h
    exact subset_al (fun j hj => (h1 j hj).1) h1 h
  · intro h
    exact h2 (Al O (C.view n m)) (fun j hj => al_nodeOK hj) (fun j hj => al_supp hj) i h

end Worklist

/-! ## Readout and the fast route -/

section Route

variable {O : Ontology (Fin n) (Fin m)} {C : CandA} {req : List (Fin n)}

theorem sorted_interA {a : Array Nat} (ha : SortedA a) (b : Array Nat) : SortedA (interA a b) := by
  unfold SortedA interA
  rw [Array.toList_filter]
  exact ha.filter _

theorem sorted_foldl_interA : ∀ (ts : List (Array Nat)) {t : Array Nat}, SortedA t →
    SortedA (ts.foldl interA t)
  | [], _, ht => ht
  | x :: ts, _, ht => by rw [List.foldl_cons]; exact sorted_foldl_interA ts (sorted_interA ht x)

theorem absLab_eq_empty {L : Array Nat} : absLab m L = ∅ ↔ L.all (fun x => decide (2 * m ≤ x)) = true := by
  rw [← Array.all_toList, List.all_eq_true, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hx
    rw [decide_eq_true_eq]
    by_contra hc
    exact h (ofRc x (by omega)) (by rw [mem_absLab, rc_ofRc]; exact Array.mem_def.2 hx)
  · intro h R hR
    have := h _ (Array.mem_def.1 (mem_absLab.1 hR))
    rw [decide_eq_true_eq] at this
    have := rc_lt R
    omega

theorem rowOfA_eq (hW : WF n m C) {A A' : Array Bool} (hA : ∀ i : Nat, A'[i]?.getD false = A[i]?.getD false)
    (k : Nat) (a : Fin n) : rowOfA (m := m) C A' k a = rowOf (C.view n m) A k a := by
  unfold rowOfA rowOf rootTys
  rw [keyOf_view]
  simp only [viewKey]
  by_cases hl : (keyA C k).lab.all (fun x => decide (2 * m ≤ x)) = true
  · rw [if_pos hl, if_pos (absLab_eq_empty.2 hl)]
    have hlist : (((memb (C.view n m) k).filter fun i => A[i]?.getD false).map
          fun i => (nd (C.view n m) i).ty).filter (fun t => decide (a ∈ t)) =
        (((membA C k).filter fun i => A'[i]?.getD false && bsA (ndA C i).ty a.val).map
          fun i => (ndA C i).ty).map (absTy n) := by
      rw [memb_view, List.filter_map, List.filter_filter, List.map_map]
      have : (fun i => (nd (C.view n m) i).ty) = absTy n ∘ fun i => (ndA C i).ty := by
        funext i; rw [view_nd_ty]; rfl
      rw [this]
      congr 1
      refine List.filter_congr fun i _ => ?_
      simp only [Function.comp_apply, hA i]
      rw [Bool.and_comm]
      congr 1
      refine decide_eq_of_iff ?_
      rw [mem_absTy, bsA_iff (hW.ty i)]
    rw [hlist]
    generalize hL : ((membA C k).filter fun i => A'[i]?.getD false && bsA (ndA C i).ty a.val).map
      (fun i => (ndA C i).ty) = L
    have hS : ∀ t ∈ L, SortedA t := by
      intro t ht
      rw [← hL] at ht
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 ht
      exact hW.ty i
    match L, hS with
    | [], _ => rfl
    | t :: ts, hS =>
      simp only [List.map_cons]
      rw [← absTy_foldl_interA ts t fun X hX => hS X (List.mem_cons_of_mem _ hX),
        sort_absTy (sorted_foldl_interA ts (hS t List.mem_cons_self))]
  · rw [if_neg hl, if_neg (fun h => hl (absLab_eq_empty.1 h))]
    rfl

theorem fastRowsA_eq (hC : WitP (mkIx O) (C.view n m)) (hW : WF n m C) :
    fastRowsA (mkIx O) C req = fastRows (mkIx O) (C.view n m) req := by
  unfold fastRowsA fastRows
  rw [view_roots]
  refine List.map_congr_left fun p _ => ?_
  rw [rowOfA_eq hW (A := aliveArr (mkIx O) (C.view n m)) (fun i => ?_)]
  have := aliveFast_iff hC hW i
  rw [Bool.eq_iff_iff, ← ap_iff, ← ap_iff]
  exact this

/-- The fast route answers as the finset route on the view. -/
theorem fastClassifyA_eq {rows : List (Fin n × Option (List (Fin n)))}
    (h : fastClassifyA O req C = some rows) : fastClassify O req (C.view n m) = some rows := by
  unfold fastClassifyA at h
  dsimp only at h
  split at h
  · next hc =>
    simp only [Option.some.injEq] at h
    subst h
    have hC := closedFastB_sound hc
    have hW : WF n m C := by
      simp only [closedFastB, Bool.and_eq_true] at hc
      exact wfB_sound hc.1.1.1.1.1
    unfold fastClassify
    dsimp only
    have hb : closedB (mkIx O) (C.view n m) req = true := decide_eq_true hC
    rw [if_pos hb, fastRowsA_eq hC.witP hW]
  · simp at h

/-- **The fast checked route is exact.** -/
theorem fastClassifyA_spec (hA : IsALCHIQ O) {rows : List (Fin n × Option (List (Fin n)))}
    (h : fastClassifyA O req C = some rows) :
    (∀ a ∈ req, ∃ p ∈ rows, p.1 = a) ∧
    ∀ p ∈ rows, p.1 ∈ req ∧
      (p.2 = none ↔
        ∀ (D : Type) [Nonempty D] (I : Interp D (Fin n) (Fin m)), models I O → ∀ x, ¬ I.c p.1 x) ∧
      ∀ L, p.2 = some L → ∀ b, b ∈ L ↔ EntailsSub O p.1 b :=
  fastClassify_spec hA (fastClassifyA_eq h)

/-- The rows of the fast route, in request order. -/
theorem fastClassifyA_get {rows : List (Fin n × Option (List (Fin n)))}
    (h : fastClassifyA O req C = some rows) {i : Nat} (hi : i < req.length) :
    ∃ p, rows[i]? = some p ∧ p.1 = req[i] :=
  fastClassify_get (fastClassifyA_eq h) hi

end Route

end ContextCalculus.SRIQ.Fast

#print axioms ContextCalculus.SRIQ.Fast.dfsG_sound
#print axioms ContextCalculus.SRIQ.Fast.dfsM_iff
#print axioms ContextCalculus.SRIQ.Fast.dfsG_complete
#print axioms ContextCalculus.SRIQ.Fast.suppF_iff
#print axioms ContextCalculus.SRIQ.Fast.elimW_spec
#print axioms ContextCalculus.SRIQ.Fast.aliveFast_iff
#print axioms ContextCalculus.SRIQ.Fast.fastRowsA_eq
#print axioms ContextCalculus.SRIQ.Fast.fastClassifyA_spec
#print axioms ContextCalculus.SRIQ.Fast.fastClassifyA_get
