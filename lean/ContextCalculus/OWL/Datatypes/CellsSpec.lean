import ContextCalculus.OWL.Datatypes.Cells

/-!
# The cells of the OWL 2 value space are exact (v1.7.0 stage C4, part C)

`cellSpec`: for every list of base atoms, every value lies in a cell of
`cellsOf as`, and every cell has exactly `cellSize as c` values
(`SRIQD.CellSpec`).
-/

namespace ContextCalculus.OWL.Datatypes

open ContextCalculus.SRIQD (toE CellSpec)

/-- `x` lies strictly inside the gap `(lo, hi)`. -/
def InGap (lo hi : Option ℚ) (x : ℝ) : Prop :=
  (∀ a ∈ lo, (a : ℝ) < x) ∧ ∀ b ∈ hi, x < (b : ℝ)

section Gap

variable {P : List ℚ} {x : ℝ}

theorem maxBelow_none (h : maxBelow P x = none) : ∀ p ∈ P, ¬ (p : ℝ) < x := by
  classical
  intro p hp hpx
  unfold maxBelow at h
  rw [List.max?_eq_none_iff] at h
  have : p ∈ P.filter fun q : ℚ => decide ((q : ℝ) < x) := List.mem_filter.2 ⟨hp, by simpa using hpx⟩
  rw [h] at this
  simp at this

theorem maxBelow_some {a : ℚ} (h : maxBelow P x = some a) :
    a ∈ P ∧ (a : ℝ) < x ∧ ∀ p ∈ P, (p : ℝ) < x → p ≤ a := by
  classical
  unfold maxBelow at h
  rw [List.max?_eq_some_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨ha, hax⟩ := List.mem_filter.1 h1
  refine ⟨ha, by simpa using hax, fun p hp hpx => h2 p (List.mem_filter.2 ⟨hp, by simpa using hpx⟩)⟩

theorem minAbove_none (h : minAbove P x = none) : ∀ p ∈ P, ¬ x < (p : ℝ) := by
  classical
  intro p hp hpx
  unfold minAbove at h
  rw [List.min?_eq_none_iff] at h
  have : p ∈ P.filter fun q : ℚ => decide (x < (q : ℝ)) := List.mem_filter.2 ⟨hp, by simpa using hpx⟩
  rw [h] at this
  simp at this

theorem minAbove_some {b : ℚ} (h : minAbove P x = some b) :
    b ∈ P ∧ x < (b : ℝ) ∧ ∀ p ∈ P, x < (p : ℝ) → b ≤ p := by
  classical
  unfold minAbove at h
  rw [List.min?_eq_some_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hb, hbx⟩ := List.mem_filter.1 h1
  refine ⟨hb, by simpa using hbx, fun p hp hpx => h2 p (List.mem_filter.2 ⟨hp, by simpa using hpx⟩)⟩

theorem maxBelow_eq_some {a : ℚ} (ha : a ∈ P) (hax : (a : ℝ) < x)
    (hmax : ∀ p ∈ P, (p : ℝ) < x → p ≤ a) : maxBelow P x = some a := by
  classical
  unfold maxBelow
  rw [List.max?_eq_some_iff]
  exact ⟨List.mem_filter.2 ⟨ha, by simpa using hax⟩, fun p hp => hmax p (List.mem_filter.1 hp).1
    (by simpa using (List.mem_filter.1 hp).2)⟩

theorem maxBelow_eq_none (h : ∀ p ∈ P, ¬ (p : ℝ) < x) : maxBelow P x = none := by
  classical
  unfold maxBelow
  rw [List.max?_eq_none_iff, List.filter_eq_nil_iff]
  intro p hp
  simpa using h p hp

theorem minAbove_eq_some {b : ℚ} (hb : b ∈ P) (hbx : x < (b : ℝ))
    (hmin : ∀ p ∈ P, x < (p : ℝ) → b ≤ p) : minAbove P x = some b := by
  classical
  unfold minAbove
  rw [List.min?_eq_some_iff]
  exact ⟨List.mem_filter.2 ⟨hb, by simpa using hbx⟩, fun p hp => hmin p (List.mem_filter.1 hp).1
    (by simpa using (List.mem_filter.1 hp).2)⟩

theorem minAbove_eq_none (h : ∀ p ∈ P, ¬ x < (p : ℝ)) : minAbove P x = none := by
  classical
  unfold minAbove
  rw [List.min?_eq_none_iff, List.filter_eq_nil_iff]
  intro p hp
  simpa using h p hp

/-- A real off the points lies in the gap of its neighbours, and that gap
is one of `gapPairs P`. -/
theorem gap_of_not_pt (hx : ∀ p ∈ P, (p : ℝ) ≠ x) :
    InGap (maxBelow P x) (minAbove P x) x ∧ (maxBelow P x, minAbove P x) ∈ gapPairs P := by
  have hin : InGap (maxBelow P x) (minAbove P x) x := by
    constructor
    · intro a ha
      exact (maxBelow_some ha).2.1
    · intro b hb
      exact (minAbove_some hb).2.1
  refine ⟨hin, ?_⟩
  unfold gapPairs
  refine List.mem_filter.2 ⟨List.mem_flatMap.2 ⟨maxBelow P x, ?_, List.mem_map.2
    ⟨minAbove P x, ?_, rfl⟩⟩, ?_⟩
  · cases h : maxBelow P x with
    | none => exact List.mem_cons_self
    | some a => exact List.mem_cons_of_mem _ (List.mem_map.2 ⟨a, (maxBelow_some h).1, rfl⟩)
  · cases h : minAbove P x with
    | none => exact List.mem_append_right _ (List.mem_singleton_self _)
    | some b => exact List.mem_append_left _ (List.mem_map.2 ⟨b, (minAbove_some h).1, rfl⟩)
  · simp only [gapOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true']
    refine ⟨?_, fun p hp => ?_⟩
    · cases h1 : maxBelow P x <;> cases h2 : minAbove P x <;> simp only [decide_eq_true_eq]
      rename_i a b
      have := (maxBelow_some h1).2.1
      have := (minAbove_some h2).2.1
      exact_mod_cast (show (a : ℝ) < b by linarith)
    · rcases lt_or_gt_of_ne (hx p hp) with hpx | hpx
      · -- `p` below `x`: at most the lower end
        cases h1 : maxBelow P x with
        | none => exact absurd hpx (maxBelow_none h1 p hp)
        | some a =>
          have := (maxBelow_some h1).2.2 p hp hpx
          simp [ltLo, not_lt.2 this]
      · cases h2 : minAbove P x with
        | none => exact absurd hpx (minAbove_none h2 p hp)
        | some b =>
          have := (minAbove_some h2).2.2 p hp hpx
          simp [ltHi, not_lt.2 this]

/-- A real inside a gap of `gapPairs P` is off the points and has that gap. -/
theorem of_mem_gapPairs {lo hi : Option ℚ} (hg : (lo, hi) ∈ gapPairs P) (hx : InGap lo hi x) :
    (∀ p ∈ P, (p : ℝ) ≠ x) ∧ maxBelow P x = lo ∧ minAbove P x = hi := by
  unfold gapPairs at hg
  obtain ⟨hmem, hok⟩ := List.mem_filter.1 hg
  obtain ⟨lo', hlo', hhi'⟩ := List.mem_flatMap.1 hmem
  obtain ⟨hi', hhi'', he⟩ := List.mem_map.1 hhi'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  simp only [gapOK, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨-, hnone⟩ := hok
  -- no point strictly inside
  have hout : ∀ p ∈ P, (p : ℝ) ≤ x → (∀ a ∈ lo', p ≤ a) ∧ (lo' = none → False) ∨ x ≤ p := by
    intro p hp hpx
    by_cases hxp : x ≤ p
    · exact Or.inr hxp
    · left
      have hpx' : (p : ℝ) < x := lt_of_not_ge hxp
      have hn := hnone p hp
      have hhi : ltHi p hi' = true := by
        cases hi' with
        | none => rfl
        | some b =>
          simp only [ltHi, decide_eq_true_eq]
          exact_mod_cast hpx'.trans (hx.2 b rfl)
      rw [hhi, Bool.and_true] at hn
      cases lo' with
      | none => simp [ltLo] at hn
      | some a =>
        simp only [ltLo, decide_eq_false_iff_not, not_lt] at hn
        exact ⟨fun a' ha' => by cases ha'; exact hn, by simp⟩
  have hout' : ∀ p ∈ P, x ≤ (p : ℝ) → (∀ b ∈ hi', b ≤ p) ∧ (hi' = none → False) ∨ (p : ℝ) ≤ x := by
    intro p hp hpx
    by_cases hxp : (p : ℝ) ≤ x
    · exact Or.inr hxp
    · left
      have hpx' : x < (p : ℝ) := lt_of_not_ge hxp
      have hn := hnone p hp
      have hlo : ltLo lo' p = true := by
        cases lo' with
        | none => rfl
        | some a =>
          simp only [ltLo, decide_eq_true_eq]
          exact_mod_cast (hx.1 a rfl).trans hpx'
      rw [hlo, Bool.true_and] at hn
      cases hi' with
      | none => simp [ltHi] at hn
      | some b =>
        simp only [ltHi, decide_eq_false_iff_not, not_lt] at hn
        exact ⟨fun b' hb' => by cases hb'; exact hn, by simp⟩
  have hnp : ∀ p ∈ P, (p : ℝ) ≠ x := by
    intro p hp hpx
    have hn := hnone p hp
    have h1 : ltLo lo' p = true := by
      cases lo' with
      | none => rfl
      | some a =>
        have := hx.1 a rfl
        rw [← hpx] at this
        simp only [ltLo, decide_eq_true_eq]
        exact_mod_cast this
    have h2 : ltHi p hi' = true := by
      cases hi' with
      | none => rfl
      | some b =>
        have := hx.2 b rfl
        rw [← hpx] at this
        simp only [ltHi, decide_eq_true_eq]
        exact_mod_cast this
    rw [h1, h2] at hn
    simp at hn
  refine ⟨hnp, ?_, ?_⟩
  · cases lo' with
    | none =>
      refine maxBelow_eq_none fun p hp hpx => ?_
      rcases hout p hp hpx.le with ⟨-, h2⟩ | h
      · exact h2 rfl
      · linarith
    | some a =>
      have haP : a ∈ P := by
        rcases List.mem_cons.1 hlo' with h | h
        · cases h
        · obtain ⟨a', ha', he⟩ := List.mem_map.1 h
          cases he
          exact ha'
      refine maxBelow_eq_some haP (hx.1 a rfl) fun p hp hpx => ?_
      rcases hout p hp hpx.le with ⟨h1, -⟩ | h
      · exact h1 a rfl
      · linarith
  · cases hi' with
    | none =>
      refine minAbove_eq_none fun p hp hpx => ?_
      rcases hout' p hp hpx.le with ⟨-, h2⟩ | h
      · exact h2 rfl
      · linarith
    | some b =>
      have hbP : b ∈ P := by
        rcases List.mem_append.1 hhi'' with h | h
        · obtain ⟨b', hb', he⟩ := List.mem_map.1 h
          cases he
          exact hb'
        · simp at h
      refine minAbove_eq_some hbP (hx.2 b rfl) fun p hp hpx => ?_
      rcases hout' p hp hpx.le with ⟨h1, -⟩ | h
      · exact h1 b rfl
      · linarith

end Gap

/-! ## Points and the cell of a value -/

section CellOf

variable {as : List BAtom}

theorem others_not_num {a : BAtom} {w : ValOf ℚ} (h : w ∈ a.others) (q : ℚ) : w ≠ .num q := by
  rcases a with k | ⟨k, bs⟩ | _ | w'
  all_goals simp only [BAtom.others, List.not_mem_nil] at h
  cases w' <;> simp_all

theorem otherPts_not_num {w : ValOf ℚ} (h : w ∈ otherPts as) (q : ℚ) : w ≠ .num q := by
  unfold otherPts at h
  rcases List.mem_append.1 (List.mem_dedup.1 h) with h | h
  · obtain ⟨a, -, ha⟩ := List.mem_flatMap.1 h
    exact others_not_num ha q
  · simp at h
    rcases h with rfl | rfl <;> simp

theorem toVal_num (q : ℚ) : toVal (.num q) = .num (q : ℝ) := rfl

theorem toVal_eq_num {w : ValOf ℚ} {x : ℝ} : toVal w = .num x ↔ ∃ q : ℚ, w = .num q ∧ (q : ℝ) = x := by
  cases w <;> simp [toVal, ValOf.map]

/-- A real is a point iff it is a numeric point. -/
theorem num_pt_iff {x : ℝ} : (∃ w ∈ allPts as, toVal w = .num x) ↔ ∃ q ∈ numPts as, (q : ℝ) = x := by
  constructor
  · rintro ⟨w, hw, he⟩
    obtain ⟨q, rfl, hq⟩ := toVal_eq_num.1 he
    rcases List.mem_append.1 hw with h | h
    · obtain ⟨q', hq', he'⟩ := List.mem_map.1 h
      cases he'
      exact ⟨q, hq', hq⟩
    · exact absurd rfl (otherPts_not_num h q)
  · rintro ⟨q, hq, rfl⟩
    exact ⟨.num q, List.mem_append_left _ (List.mem_map_of_mem hq), rfl⟩

theorem restCell_ne_pt (v : Val) (w : ValOf ℚ) : restCell v ≠ .pt w := by
  rcases v with x | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, z⟩ | s | n <;>
    simp only [restCell] <;> (try split_ifs) <;> simp

theorem restCell_ne_gap (v : Val) (lo hi : Option ℚ) (c : Fin 3) : restCell v ≠ .gap lo hi c := by
  rcases v with x | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, z⟩ | s | n <;>
    simp only [restCell] <;> (try split_ifs) <;> simp

theorem restCell_mem (v : Val) : restCell v ∈ restCells := by
  rcases v with x | x | x | ⟨s, _ | t⟩ | b | bs | bs | s | ⟨t, z⟩ | s | n <;>
    simp only [restCell] <;> (try split_ifs) <;> simp [restCells]

theorem cellOf_pt {w : ValOf ℚ} (hw : w ∈ allPts as) : cellOf as (toVal w) = .pt w := by
  classical
  have h : ∃ w' ∈ allPts as, toVal w' = toVal w := ⟨w, hw, rfl⟩
  unfold cellOf
  rw [dif_pos h]
  congr 1
  exact toVal_injective h.choose_spec.2

theorem cellOf_eq_pt_iff {v : Val} {w : ValOf ℚ} :
    cellOf as v = .pt w ↔ w ∈ allPts as ∧ toVal w = v := by
  classical
  constructor
  · intro hc
    unfold cellOf at hc
    split_ifs at hc with h
    · cases hc
      exact h.choose_spec
    · cases v with
      | num x => cases hc
      | _ => exact absurd hc (restCell_ne_pt _ _)
  · rintro ⟨hw, rfl⟩
    exact cellOf_pt hw

theorem cellOf_num_gap {x : ℝ} (hx : ∀ q ∈ numPts as, (q : ℝ) ≠ x) :
    cellOf as (.num x) = .gap (maxBelow (numPts as) x) (minAbove (numPts as) x) (numClass x) := by
  classical
  have h : ¬ ∃ w ∈ allPts as, toVal w = .num x := fun h => by
    obtain ⟨q, hq, he⟩ := num_pt_iff.1 h
    exact hx q hq he
  unfold cellOf
  rw [dif_neg h]

theorem cellOf_rest {v : Val} (hv : ¬ ∃ w ∈ allPts as, toVal w = v) (hn : ∀ x, v ≠ .num x) :
    cellOf as v = restCell v := by
  classical
  unfold cellOf
  rw [dif_neg hv]
  cases v with
  | num x => exact absurd rfl (hn x)
  | _ => rfl

/-- Every value lies in a cell of the list. -/
theorem cellOf_mem (v : Val) : cellOf as v ∈ cellsOf as := by
  classical
  unfold cellsOf
  rw [List.mem_dedup]
  by_cases hv : ∃ w ∈ allPts as, toVal w = v
  · obtain ⟨w, hw, rfl⟩ := hv
    rw [cellOf_pt hw]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hw))
  · cases v with
    | num x =>
      have hx : ∀ q ∈ numPts as, (q : ℝ) ≠ x := fun q hq he => hv (num_pt_iff.2 ⟨q, hq, he⟩)
      rw [cellOf_num_gap hx]
      refine List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2
        ⟨_, (gap_of_not_pt hx).2, ?_⟩))
      simp only [List.mem_cons, List.mem_map, List.not_mem_nil]
      generalize numClass x = c
      fin_cases c <;> simp
    | _ =>
      rw [cellOf_rest hv (by intro x h; cases h)]
      exact List.mem_append_right _ (restCell_mem _)

/-- The values of a gap cell. -/
theorem cellOf_eq_gap_iff {v : Val} {lo hi : Option ℚ} {c : Fin 3} (hg : (lo, hi) ∈ gapPairs (numPts as)) :
    cellOf as v = .gap lo hi c ↔ ∃ x, v = .num x ∧ InGap lo hi x ∧ numClass x = c := by
  classical
  constructor
  · intro hc
    by_cases hv : ∃ w ∈ allPts as, toVal w = v
    · obtain ⟨w, hw, rfl⟩ := hv
      rw [cellOf_pt hw] at hc
      cases hc
    · cases v with
      | num x =>
        have hx : ∀ q ∈ numPts as, (q : ℝ) ≠ x := fun q hq he => hv (num_pt_iff.2 ⟨q, hq, he⟩)
        rw [cellOf_num_gap hx] at hc
        simp only [Cell.gap.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        exact ⟨x, rfl, (gap_of_not_pt hx).1, rfl⟩
      | _ =>
        rw [cellOf_rest hv (by intro x h; cases h)] at hc
        exact absurd hc (restCell_ne_gap _ _ _ _)
  · rintro ⟨x, rfl, hx, rfl⟩
    obtain ⟨hnp, h1, h2⟩ := of_mem_gapPairs hg hx
    rw [cellOf_num_gap hnp, h1, h2]

end CellOf

/-! ## Classes of reals and witnesses -/

section Witness

theorem numClass_zero {x : ℝ} : numClass x = 0 ↔ ∃ z : ℤ, x = z := by
  classical
  unfold numClass
  split_ifs with h1 h2 <;> simp_all

theorem numClass_one {x : ℝ} : numClass x = 1 ↔ (¬ ∃ z : ℤ, x = z) ∧ IsDecimalR x := by
  classical
  unfold numClass
  split_ifs with h1 h2 <;> simp_all

theorem numClass_two {x : ℝ} : numClass x = 2 ↔ (¬ ∃ z : ℤ, x = z) ∧ ¬ IsDecimalR x := by
  classical
  unfold numClass
  split_ifs with h1 h2 <;> simp_all

theorem isDecimalR_cast (q : ℚ) : IsDecimalR (q : ℝ) ↔ IsDecimalQ q := by
  constructor
  · rintro ⟨z, k, h⟩
    refine ⟨z, k, ?_⟩
    exact_mod_cast h
  · rintro ⟨z, k, h⟩
    refine ⟨z, k, ?_⟩
    rw [h]
    push_cast
    rfl

theorem rat_of_isDecimalR {x : ℝ} (h : IsDecimalR x) : ∃ q : ℚ, x = q := by
  obtain ⟨z, k, rfl⟩ := h
  exact ⟨(z : ℚ) / 10 ^ k, by push_cast; rfl⟩

/-- Infinitely many decimals that are not integers between two rationals. -/
theorem dec_witness {c d : ℚ} (hcd : c < d) :
    ∃ f : ℕ → ℝ, Function.Injective f ∧ ∀ n, (c : ℝ) < f n ∧ f n < d ∧ numClass (f n) = 1 := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 / (d - c)) (show (1 : ℚ) < 10 by norm_num)
  have hdc : 0 < d - c := sub_pos.2 hcd
  have hk' : 2 / (10 : ℚ) ^ k < d - c := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hdc] at hk
    linarith
  let z : ℤ := ⌊c * 10 ^ k⌋ + 1
  have hz1 : c < (z : ℚ) / 10 ^ k := by
    rw [lt_div_iff₀ (by positivity)]
    have := Int.lt_floor_add_one (c * 10 ^ k)
    push_cast [z]
    linarith
  have hz2 : (z : ℚ) / 10 ^ k ≤ c + 1 / 10 ^ k := by
    rw [div_le_iff₀ (by positivity), add_mul, one_div, inv_mul_cancel₀ (by positivity)]
    have := Int.floor_le (c * 10 ^ k)
    push_cast [z]
    linarith
  let g : ℕ → ℚ := fun n => (z : ℚ) / 10 ^ k + 1 / 10 ^ (k + n + 1)
  refine ⟨fun n => ((g n : ℚ) : ℝ), ?_, fun n => ⟨?_, ?_, ?_⟩⟩
  · intro n n' h
    simp only at h
    have h' : g n = g n' := by exact_mod_cast h
    simp only [g, add_right_inj, one_div, inv_inj] at h'
    have h'' : (10 : ℕ) ^ (k + n + 1) = 10 ^ (k + n' + 1) := by exact_mod_cast h'
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 10) h''
    omega
  · have : c < g n := by
      have : (0 : ℚ) < 1 / 10 ^ (k + n + 1) := by positivity
      simp only [g]; linarith
    show (c : ℝ) < (g n : ℝ)
    exact_mod_cast this
  · have : g n < d := by
      have h1 : (1 : ℚ) / 10 ^ (k + n + 1) ≤ 1 / 10 ^ k := by
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (1 : ℚ) / 10 ^ k + 1 / 10 ^ k = 2 / 10 ^ k := by ring
      simp only [g]; linarith
    show (g n : ℝ) < d
    exact_mod_cast this
  · show numClass (g n : ℝ) = 1
    rw [numClass_one]
    have hg : g n = ((z * 10 ^ (n + 1) + 1 : ℤ) : ℚ) / 10 ^ (k + n + 1) := by
      simp only [g]
      push_cast
      field_simp
      ring
    refine ⟨?_, (isDecimalR_cast _).2 ⟨_, _, hg⟩⟩
    rintro ⟨w, hw⟩
    have hw' : g n = w := by exact_mod_cast hw
    rw [hg, div_eq_iff (by positivity)] at hw'
    have hint : (z * 10 ^ (n + 1) + 1 : ℤ) = w * 10 ^ (k + n + 1) := by exact_mod_cast hw'
    have e1 : (10 : ℤ) ^ (n + 1) = 10 * 10 ^ n := by ring
    have e2 : (10 : ℤ) ^ (k + n + 1) = 10 * 10 ^ (k + n) := by ring
    rw [e1, e2] at hint
    have : (10 : ℤ) * (z * 10 ^ n) + 1 = 10 * (w * 10 ^ (k + n)) := by linarith
    omega

theorem sqrt_two_lt_two : √2 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

/-- Infinitely many reals that are not decimals between two rationals. -/
theorem other_witness {c d : ℚ} (hcd : c < d) :
    ∃ f : ℕ → ℝ, Function.Injective f ∧ ∀ n, (c : ℝ) < f n ∧ f n < d ∧ numClass (f n) = 2 := by
  have hdc : (0 : ℝ) < d - c := by exact_mod_cast sub_pos.2 hcd
  have hs1 : 0 < √2 - 1 := by linarith [Real.one_lt_sqrt_two]
  have hs2 : √2 - 1 < 1 := by linarith [sqrt_two_lt_two]
  let f : ℕ → ℝ := fun n => c + (d - c) * ((√2 - 1) / (n + 2))
  refine ⟨f, ?_, fun n => ⟨?_, ?_, ?_⟩⟩
  · intro n n' h
    simp only [f, add_right_inj] at h
    have h2 : (√2 - 1) / ((n : ℝ) + 2) = (√2 - 1) / ((n' : ℝ) + 2) :=
      mul_left_cancel₀ hdc.ne' h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h2
    have : ((n : ℝ) + 2) = n' + 2 := by
      have := mul_left_cancel₀ hs1.ne' (by linarith : (√2 - 1) * ((n' : ℝ) + 2) = (√2 - 1) * (n + 2))
      linarith
    exact_mod_cast (by linarith : (n : ℝ) = n')
  · have : 0 < (d - c) * ((√2 - 1) / ((n : ℝ) + 2)) := by positivity
    simp only [f]; linarith
  · have h1 : (√2 - 1) / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have : (d - c) * ((√2 - 1) / ((n : ℝ) + 2)) < (d - c) * 1 := mul_lt_mul_of_pos_left h1 hdc
    simp only [f]; push_cast at this ⊢; linarith
  · have hirr : Irrational (f n) := by
      have h1 : Irrational (√2 - 1) := by
        have := irrational_sqrt_two.sub_intCast 1
        simpa using this
      have hq : ((d - c) / (n + 2) : ℚ) ≠ 0 := by
        have : (0 : ℚ) < (n : ℚ) + 2 := by positivity
        exact div_ne_zero (sub_pos.2 hcd).ne' this.ne'
      have h2 := (h1.ratCast_mul hq).ratCast_add c
      convert h2 using 1
      simp only [f]
      push_cast
      ring
    rw [numClass_two]
    refine ⟨?_, fun hd => ?_⟩
    · rintro ⟨z, hz⟩
      exact hirr ⟨z, by rw [hz]; push_cast; rfl⟩
    · obtain ⟨q, hq⟩ := rat_of_isDecimalR hd
      exact hirr ⟨q, hq.symm⟩

end Witness

end ContextCalculus.OWL.Datatypes
