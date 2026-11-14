import ContextCalculus.OWL.Datatypes.Map
import Mathlib.Data.Set.Card

/-!
# The order of IEEE floats as integers (v1.7.0 stage C4)

`FloatV.ord` numbers the floats in their facet order: a finite float with
sign `s`, biased exponent `E` and fraction `M` is `±(E·2^m + M)`, the
infinities are `±N` with `N = (2^e - 1)·2^m`. Both zeros are `0`; NaN gets
`0` as well but takes no part in the order (`FloatV.key` is `none`).

`key_lt_iff`, `key_eq_iff`: on floats other than NaN the order of
`FloatV.key` is the order of `ord`. So a bound facet on floats compares
`ord` values (`floatRel_iff`).
-/

namespace ContextCalculus.OWL.Datatypes

namespace FloatV

variable {e m : Nat}

/-- The magnitude of the finite float with index `i = E·2^m + M`, in units
of the smallest subnormal. -/
def gN (m i : Nat) : Nat :=
  if i / 2 ^ m = 0 then i % 2 ^ m else (2 ^ m + i % 2 ^ m) * 2 ^ (i / 2 ^ m - 1)

theorem gN_lt (m i : Nat) : gN m i < 2 ^ m * 2 ^ (i / 2 ^ m) := by
  have hM := Nat.mod_lt i (Nat.two_pow_pos m)
  unfold gN
  split_ifs with h
  · rw [h]; simpa using hM
  · obtain ⟨E, hE⟩ : ∃ E, i / 2 ^ m = E + 1 :=
      ⟨i / 2 ^ m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero h)).symm⟩
    rw [hE, Nat.add_sub_cancel, pow_succ]
    have : 2 ^ m + i % 2 ^ m < 2 ^ m * 2 := by omega
    calc (2 ^ m + i % 2 ^ m) * 2 ^ E < (2 ^ m * 2) * 2 ^ E :=
          Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos E)
      _ = 2 ^ m * (2 ^ E * 2) := by ring

theorem le_gN (m i : Nat) (h : i / 2 ^ m ≠ 0) : 2 ^ m * 2 ^ (i / 2 ^ m - 1) ≤ gN m i := by
  unfold gN
  rw [if_neg h]
  exact Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

theorem gN_strictMono (m : Nat) : StrictMono (gN m) := by
  intro i j hij
  have hq : i / 2 ^ m ≤ j / 2 ^ m := Nat.div_le_div_right hij.le
  rcases hq.lt_or_eq with hlt | heq
  · have h1 := gN_lt m i
    have h2 := le_gN m j (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hlt))
    have h3 : 2 ^ m * 2 ^ (i / 2 ^ m) ≤ 2 ^ m * 2 ^ (j / 2 ^ m - 1) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_sub_one_of_lt hlt))
    exact lt_of_lt_of_le h1 (h3.trans h2)
  · have hmod : i % 2 ^ m < j % 2 ^ m := by
      have := Nat.div_add_mod i (2 ^ m)
      have := Nat.div_add_mod j (2 ^ m)
      rw [heq] at *
      omega
    unfold gN
    rw [heq]
    split_ifs
    · exact hmod
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

theorem gN_zero (m : Nat) : gN m 0 = 0 := by simp [gN]

/-- The facet order of the floats as integers (see the module docstring). -/
def ord : FloatV e m → Int
  | fin neg E M => if neg then -((E.val * 2 ^ m + M.val : Nat) : Int) else ((E.val * 2 ^ m + M.val : Nat) : Int)
  | inf neg => if neg then -(((2 ^ e - 1) * 2 ^ m : Nat) : Int) else (((2 ^ e - 1) * 2 ^ m : Nat) : Int)
  | nan => 0

/-- The unit: the smallest subnormal. -/
def unit (e m : Nat) : ℚ := (2 : ℚ) ^ (1 - bias e - (m : Int))

theorem unit_pos (e m : Nat) : 0 < unit e m := zpow_pos (by norm_num) _

/-- The signed magnitude of an index. -/
def sval (e m : Nat) (z : Int) : ℚ :=
  if 0 ≤ z then (gN m z.toNat : ℚ) * unit e m else -((gN m (-z).toNat : ℚ) * unit e m)

theorem sval_strictMono (e m : Nat) : StrictMono (sval e m) := by
  intro a b hab
  have hu := unit_pos e m
  have hmono := gN_strictMono m
  unfold sval
  split_ifs with ha hb hb
  · have : a.toNat < b.toNat := by omega
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hmono this) hu
  · omega
  · have h0 : (0 : ℚ) ≤ (gN m (-a).toNat : ℚ) * unit e m := by positivity
    have h1 : (0 : ℚ) < (gN m (-a).toNat : ℚ) * unit e m := by
      apply mul_pos _ hu
      have : 0 < (-a).toNat := by omega
      have := hmono this
      rw [gN_zero] at this
      exact_mod_cast this
    have h2 : (0 : ℚ) ≤ (gN m b.toNat : ℚ) * unit e m := by positivity
    linarith
  · have : (-b).toNat < (-a).toNat := by omega
    have := mul_lt_mul_of_pos_right (show (gN m (-b).toNat : ℚ) < gN m (-a).toNat by
      exact_mod_cast hmono this) hu
    linarith

theorem idx_div {E M : Nat} (hM : M < 2 ^ m) : (E * 2 ^ m + M) / 2 ^ m = E := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt hM, zero_add]

theorem idx_mod {E M : Nat} (hM : M < 2 ^ m) : (E * 2 ^ m + M) % 2 ^ m = M := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hM]

theorem toRat?_fin (neg : Bool) (E : Fin (2 ^ e - 1)) (M : Fin (2 ^ m)) :
    (fin neg E M).toRat? = some (sval e m (fin neg E M : FloatV e m).ord) := by
  have hg : ((gN m (E.val * 2 ^ m + M.val) : Nat) : ℚ) * unit e m =
      if E.val = 0 then (M.val : ℚ) * (2 : ℚ) ^ (1 - bias e - (m : Int))
      else ((2 ^ m + M.val : Nat) : ℚ) * (2 : ℚ) ^ ((E.val : Int) - bias e - (m : Int)) := by
    unfold gN unit
    rw [idx_div M.isLt, idx_mod M.isLt]
    split_ifs with h0
    · rfl
    · push_cast
      rw [mul_assoc]
      congr 1
      rw [← zpow_natCast, ← zpow_add₀ two_ne_zero]
      congr 1
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 h0)]
      ring
  have hX : (fin neg E M : FloatV e m).toRat? = some (if neg then
      -((gN m (E.val * 2 ^ m + M.val) : ℚ) * unit e m)
      else (gN m (E.val * 2 ^ m + M.val) : ℚ) * unit e m) := by
    simp only [toRat?]
    rw [hg]
  rw [hX]
  congr 1
  cases neg
  · simp only [Bool.false_eq_true, if_false, ord, sval]
    rw [if_pos (Int.natCast_nonneg _), Int.toNat_natCast]
  · simp only [if_true, ord, sval]
    by_cases hz : E.val * 2 ^ m + M.val = 0
    · rw [hz]; simp [gN_zero]
    · rw [if_neg (by omega), neg_neg, Int.toNat_natCast]

/-- The largest finite index is below the index of the infinities. -/
theorem fin_idx_lt (E : Fin (2 ^ e - 1)) (M : Fin (2 ^ m)) :
    E.val * 2 ^ m + M.val < (2 ^ e - 1) * 2 ^ m := by
  have hE : E.val + 1 ≤ 2 ^ e - 1 := E.isLt
  have : (E.val + 1) * 2 ^ m ≤ (2 ^ e - 1) * 2 ^ m := Nat.mul_le_mul_right _ hE
  have hM := M.isLt
  nlinarith

/-- The index of the infinities. -/
def top (e m : Nat) : Int := (((2 ^ e - 1) * 2 ^ m : Nat) : Int)

/-- The key of an index. -/
def phi (e m : Nat) (z : Int) : WithBot (WithTop ℚ) :=
  if z ≤ -top e m then ⊥ else if top e m ≤ z then ⊤ else (((sval e m z : ℚ) : WithTop ℚ) : WithBot (WithTop ℚ))

theorem phi_strictMonoOn (e m : Nat) : StrictMonoOn (phi e m) (Set.Icc (-top e m) (top e m)) := by
  rintro a ⟨ha1, ha2⟩ b ⟨hb1, hb2⟩ hab
  unfold phi
  by_cases h1 : a ≤ -top e m
  · rw [if_pos h1, if_neg (by omega)]
    split_ifs
    · exact WithBot.bot_lt_coe _
    · exact WithBot.bot_lt_coe _
  · rw [if_neg h1, if_neg (by omega : ¬ top e m ≤ a), if_neg (by omega : ¬ b ≤ -top e m)]
    split_ifs with h2
    · exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top _)
    · exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 (sval_strictMono e m hab))

theorem key_phi (he : 1 ≤ e) (x : FloatV e m) (hx : x ≠ nan) :
    x.key = some (phi e m x.ord) ∧ x.ord ∈ Set.Icc (-top e m) (top e m) := by
  have hN : 0 < top e m := by
    unfold top
    have : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    have : 0 < (2 ^ e - 1) * 2 ^ m := Nat.mul_pos (by omega) (Nat.two_pow_pos m)
    exact_mod_cast this
  cases x with
  | nan => exact absurd rfl hx
  | inf s =>
    cases s
    · refine ⟨?_, ?_⟩
      · simp only [key, ord, Bool.false_eq_true, if_false, phi]
        rw [if_neg (by unfold top at hN ⊢; omega), if_pos (by unfold top; exact le_refl _)]
      · simp only [ord, Bool.false_eq_true, if_false, Set.mem_Icc]
        unfold top at hN ⊢; omega
    · refine ⟨?_, ?_⟩
      · simp only [key, ord, if_true, phi]
        rw [if_pos (by unfold top; omega)]
      · simp only [ord, if_true, Set.mem_Icc]
        unfold top at hN ⊢; omega
  | fin neg E M =>
    have hi := fin_idx_lt E M
    have hb : (fin neg E M : FloatV e m).ord ∈ Set.Icc (-top e m + 1) (top e m - 1) := by
      unfold top
      cases neg <;> simp only [ord, Bool.false_eq_true, if_false, if_true, Set.mem_Icc] <;> omega
    refine ⟨?_, ⟨by linarith [hb.1], by linarith [hb.2]⟩⟩
    simp only [key, toRat?_fin, phi]
    rw [if_neg (by linarith [hb.1]), if_neg (by linarith [hb.2])]
    rfl

/-- **The facet order is the order of `ord`.** -/
theorem key_lt_iff (he : 1 ≤ e) {x y : FloatV e m} (hx : x ≠ nan) (hy : y ≠ nan)
    {kx ky : WithBot (WithTop ℚ)} (hkx : x.key = some kx) (hky : y.key = some ky) :
    kx < ky ↔ x.ord < y.ord := by
  obtain ⟨h1, h2⟩ := key_phi he x hx
  obtain ⟨h3, h4⟩ := key_phi he y hy
  rw [hkx, Option.some.injEq] at h1
  rw [hky, Option.some.injEq] at h3
  rw [h1, h3]
  exact (phi_strictMonoOn e m).lt_iff_lt h2 h4

theorem key_le_iff (he : 1 ≤ e) {x y : FloatV e m} (hx : x ≠ nan) (hy : y ≠ nan)
    {kx ky : WithBot (WithTop ℚ)} (hkx : x.key = some kx) (hky : y.key = some ky) :
    kx ≤ ky ↔ x.ord ≤ y.ord := by
  obtain ⟨h1, h2⟩ := key_phi he x hx
  obtain ⟨h3, h4⟩ := key_phi he y hy
  rw [hkx, Option.some.injEq] at h1
  rw [hky, Option.some.injEq] at h3
  rw [h1, h3]
  exact (phi_strictMonoOn e m).le_iff_le h2 h4

theorem key_isSome {x : FloatV e m} (hx : x ≠ nan) : ∃ k, x.key = some k := by
  cases x with
  | nan => exact absurd rfl hx
  | inf s => cases s <;> exact ⟨_, rfl⟩
  | fin neg E M => exact ⟨_, by simp only [key, toRat?_fin]; rfl⟩

/-- **A bound facet on floats compares `ord`.** -/
theorem floatRel_iff (he : 1 ≤ e) (b : Bool × Bool) (x y : FloatV e m) :
    floatRel b x y ↔ x ≠ nan ∧ y ≠ nan ∧ boundRel b x.ord y.ord := by
  constructor
  · rintro ⟨kx, ky, hkx, hky, h⟩
    have hx : x ≠ nan := by rintro rfl; simp [key] at hkx
    have hy : y ≠ nan := by rintro rfl; simp [key] at hky
    refine ⟨hx, hy, ?_⟩
    rcases b with ⟨_ | _, _ | _⟩ <;> simp only [boundRel] at h ⊢
    · exact (key_le_iff he hx hy hkx hky).1 h
    · exact (key_lt_iff he hx hy hkx hky).1 h
    · exact (key_le_iff he hy hx hky hkx).1 h
    · exact (key_lt_iff he hy hx hky hkx).1 h
  · rintro ⟨hx, hy, h⟩
    obtain ⟨kx, hkx⟩ := key_isSome hx
    obtain ⟨ky, hky⟩ := key_isSome hy
    refine ⟨kx, ky, hkx, hky, ?_⟩
    rcases b with ⟨_ | _, _ | _⟩ <;> simp only [boundRel] at h ⊢
    · exact (key_le_iff he hx hy hkx hky).2 h
    · exact (key_lt_iff he hx hy hkx hky).2 h
    · exact (key_le_iff he hy hx hky hkx).2 h
    · exact (key_lt_iff he hy hx hky hkx).2 h

/-! ## Counting floats by `ord` -/

/-- The float with index `z ≥ 0` and sign `neg` (`nan` outside the range). -/
def ofIdx (neg : Bool) (i : Nat) : FloatV e m :=
  if h : i < (2 ^ e - 1) * 2 ^ m then
    fin neg ⟨i / 2 ^ m, (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m)).2 h⟩ ⟨i % 2 ^ m, Nat.mod_lt _ (Nat.two_pow_pos m)⟩
  else if i = (2 ^ e - 1) * 2 ^ m then inf neg else nan

/-- The float of an index (`+0` at `0`). -/
def canon (z : Int) : FloatV e m := if 0 ≤ z then ofIdx false z.toNat else ofIdx true (-z).toNat

/-- Negative zero (`nan` without finite floats). -/
def negZero : FloatV e m := ofIdx true 0

theorem ord_ofIdx (neg : Bool) {i : Nat} (hi : i ≤ (2 ^ e - 1) * 2 ^ m) :
    (ofIdx neg i : FloatV e m).ord = (if neg then -(i : Int) else (i : Int)) ∧
      (ofIdx neg i : FloatV e m) ≠ nan := by
  unfold ofIdx
  by_cases h1 : i < (2 ^ e - 1) * 2 ^ m
  · rw [dif_pos h1]
    refine ⟨?_, by simp⟩
    have hdm : i / 2 ^ m * 2 ^ m + i % 2 ^ m = i := Nat.div_add_mod' i (2 ^ m)
    cases neg <;> simp [ord, hdm]
  · have h2 : i = (2 ^ e - 1) * 2 ^ m := by omega
    rw [dif_neg h1, if_pos h2]
    refine ⟨?_, by simp⟩
    cases neg <;> simp [ord, h2]

theorem canon_spec {z : Int} (hz : z ∈ Set.Icc (-top e m) (top e m)) :
    (canon z : FloatV e m).ord = z ∧ (canon z : FloatV e m) ≠ nan := by
  obtain ⟨h1, h2⟩ := hz
  unfold top at h1 h2
  unfold canon
  split_ifs with h
  · have := ord_ofIdx (e := e) (m := m) false (i := z.toNat) (by omega)
    simp only [Bool.false_eq_true, if_false] at this
    exact ⟨by rw [this.1]; omega, this.2⟩
  · have := ord_ofIdx (e := e) (m := m) true (i := (-z).toNat) (by omega)
    simp only [if_true] at this
    exact ⟨by rw [this.1]; omega, this.2⟩

theorem ord_mem (he : 1 ≤ e) {x : FloatV e m} (hx : x ≠ nan) :
    x.ord ∈ Set.Icc (-top e m) (top e m) := (key_phi he x hx).2

/-- A float other than NaN is the float of its index, or negative zero. -/
theorem eq_canon (he : 1 ≤ e) {x : FloatV e m} (hx : x ≠ nan) : x = canon x.ord ∨ x = negZero := by
  cases x with
  | nan => exact absurd rfl hx
  | inf s =>
    left
    have hpos : 0 < (2 ^ e - 1) * 2 ^ m :=
      Nat.mul_pos (by have := Nat.one_lt_two_pow (n := e) (by omega); omega) (Nat.two_pow_pos m)
    cases s
    · show inf false = canon (((2 ^ e - 1) * 2 ^ m : Nat) : Int)
      unfold canon
      rw [if_pos (Int.natCast_nonneg _), Int.toNat_natCast]
      unfold ofIdx
      rw [dif_neg (lt_irrefl _), if_pos rfl]
    · show inf true = canon (-(((2 ^ e - 1) * 2 ^ m : Nat) : Int))
      unfold canon
      rw [if_neg (by omega), neg_neg, Int.toNat_natCast]
      unfold ofIdx
      rw [dif_neg (lt_irrefl _), if_pos rfl]
  | fin neg E M =>
    have hi := fin_idx_lt E M
    have hd := idx_div (E := E.val) M.isLt
    have hmd := idx_mod (E := E.val) M.isLt
    cases neg
    · left
      simp only [ord, Bool.false_eq_true, if_false, canon, Int.natCast_nonneg, if_true, Int.toNat_natCast,
        ofIdx, dif_pos hi]
      congr 1 <;> ext <;> simp [hd, hmd]
    · by_cases h0 : E.val * 2 ^ m + M.val = 0
      · right
        have hE : E.val * 2 ^ m = 0 := by omega
        have hE' : E.val = 0 := by
          rcases Nat.mul_eq_zero.1 hE with h | h
          · exact h
          · exact absurd h (Nat.two_pow_pos m).ne'
        have hM : M.val = 0 := by omega
        have hpos : 0 < (2 ^ e - 1) * 2 ^ m := by omega
        simp only [negZero, ofIdx, dif_pos hpos]
        congr 1 <;> ext <;> simp [hE', hM]
      · left
        simp only [ord, if_true, canon]
        rw [if_neg (by omega), neg_neg, Int.toNat_natCast]
        simp only [ofIdx, dif_pos hi]
        congr 1 <;> ext <;> simp [hd, hmd]

theorem negZero_spec (he : 1 ≤ e) :
    (negZero : FloatV e m).ord = 0 ∧ (negZero : FloatV e m) ≠ nan ∧
      (negZero : FloatV e m) ≠ canon 0 := by
  have hpos : 0 < (2 ^ e - 1) * 2 ^ m :=
    Nat.mul_pos (by have := Nat.one_lt_two_pow (n := e) (by omega); omega) (Nat.two_pow_pos m)
  have := ord_ofIdx (e := e) (m := m) true (i := 0) (by omega)
  refine ⟨by simpa using this.1, this.2, ?_⟩
  simp [negZero, canon, ofIdx, hpos]

open Classical in
/-- **Counting floats by index.** For a set `S` of indices in range, the
floats other than NaN with index in `S` are the elements of `S` and, when
`0 ∈ S`, negative zero. -/
theorem encard_ord (he : 1 ≤ e) {S : Set Int} (hS : S ⊆ Set.Icc (-top e m) (top e m)) :
    ({x : FloatV e m | x ≠ nan ∧ x.ord ∈ S} : Set (FloatV e m)).encard =
      Set.encard S + (if (0 : Int) ∈ S then 1 else 0) := by
  have hinj : Set.InjOn (canon : Int → FloatV e m) S := fun a ha b hb h => by
    have h1 := (canon_spec (e := e) (m := m) (hS ha)).1
    have h2 := (canon_spec (e := e) (m := m) (hS hb)).1
    rw [← h1, ← h2, h]
  obtain ⟨hz1, hz2, hz3⟩ := negZero_spec (m := m) he
  have hset : {x : FloatV e m | x ≠ nan ∧ x.ord ∈ S} =
      canon '' S ∪ (if (0 : Int) ∈ S then {negZero} else ∅) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hx, hxs⟩
      rcases eq_canon he hx with h | h
      · exact Or.inl ⟨_, hxs, h.symm⟩
      · right
        subst h
        rw [hz1] at hxs
        simp [hxs]
    · rintro (⟨z, hz, rfl⟩ | h)
      · have := canon_spec (e := e) (m := m) (hS hz)
        exact ⟨this.2, by rw [this.1]; exact hz⟩
      · split_ifs at h with h0
        · rw [Set.mem_singleton_iff] at h
          subst h
          exact ⟨hz2, by rw [hz1]; exact h0⟩
        · exact absurd h (Set.notMem_empty _)
  rw [hset, Set.encard_union_eq, hinj.encard_image]
  · split_ifs <;> simp
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ h
    split_ifs at h
    · rw [Set.mem_singleton_iff] at h
      have h1 := (canon_spec (e := e) (m := m) (hS hz)).1
      rw [h, hz1] at h1
      subst h1
      exact hz3 h.symm
    · exact h

end FloatV

end ContextCalculus.OWL.Datatypes

#print axioms ContextCalculus.OWL.Datatypes.FloatV.floatRel_iff
#print axioms ContextCalculus.OWL.Datatypes.FloatV.encard_ord
