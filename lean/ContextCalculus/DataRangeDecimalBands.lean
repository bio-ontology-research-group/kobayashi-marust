import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card

/-!
# Sizes of the decimal-tower cells (`vocabulary.rs`, `decimal_cells`)

The cells of a decimal-tower partition are the endpoints (points), and in
every open gap `(a, b)` between consecutive endpoints the bands of the value
kinds present in the group: the integers of the gap, then the decimals that
are not integers, the rationals that are not decimals, the reals that are
not rationals (OWL 2 Structural Specification 4.1: `owl:real ⊃ owl:rational
⊃ xsd:decimal ⊃ xsd:integer`). `Cell::size` is the integer count for the
integer band and infinite for the others. This file proves those sizes for
the value spaces themselves:

* `int_band_encard`: `[a, b] ∩ ℤ` has `b + 1 - a` elements;
* `decimal_band_infinite`, `rational_band_infinite`, `real_band_infinite`:
  each non-integer band of a nonempty open interval is infinite, so
  `size = ⊤` is the value `CellSpec.size_eq` of `DataRangeCells` asks for.

(The rational endpoints of the gap are what `decimal_cells` computes; the
IEEE segment sizes are rank differences of `FloatRange::unrank` and stay
assumed.)
-/

namespace ContextCalculus.DataRangeDecimalBands

/-- The integer band `[a, b]`. -/
theorem int_band_encard (a b : ℤ) : (Set.Icc a b).encard = ((b + 1 - a).toNat : ℕ∞) := by
  rw [← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]

/-- The `xsd:decimal` value space inside `ℚ`: finite decimal fractions. -/
def IsDecimal (q : ℚ) : Prop := ∃ k : ℕ, ∃ m : ℤ, q = m / 10 ^ k

theorem isDecimal_add {p q : ℚ} : IsDecimal p → IsDecimal q → IsDecimal (p + q) := by
  rintro ⟨k, m, rfl⟩ ⟨k', m', rfl⟩
  refine ⟨k + k', m * 10 ^ k' + m' * 10 ^ k, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

theorem isDecimal_inv_pow (n : ℕ) : IsDecimal (1 / 10 ^ n) := ⟨n, 1, by simp⟩

theorem isDecimal_int (z : ℤ) : IsDecimal z := ⟨0, z, by simp⟩

section Field
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem exists_small [Archimedean K] (ε : K) (h : 0 < ε) : ∃ n : ℕ, (1 : K) / 10 ^ n < ε := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h (show (1 / 10 : K) < 1 by norm_num)
  exact ⟨n, by rwa [div_pow, one_pow] at hn⟩

theorem inv_pow_injective : Function.Injective (fun n : ℕ => (1 : K) / 10 ^ n) := by
  intro i j hij
  simp only [one_div, inv_inj] at hij
  exact (pow_right_strictMono₀ (by norm_num : (1 : K) < 10)).injective hij

theorem inv_pow_le (M j : ℕ) : (1 : K) / 10 ^ (M + j) ≤ 1 / 10 ^ M :=
  one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))

end Field

theorem exists_decimal_btwn {a c : ℚ} (h : a < c) : ∃ d, IsDecimal d ∧ a < d ∧ d < c := by
  obtain ⟨n, hn⟩ := exists_small (c - a) (by linarith)
  have hp : (0 : ℚ) < 10 ^ n := by positivity
  have h1 : 1 < (c - a) * 10 ^ n := (div_lt_iff₀ hp).1 hn
  have hfl : (⌊a * 10 ^ n⌋ : ℚ) ≤ a * 10 ^ n := Int.floor_le _
  have hlt : a * 10 ^ n < (⌊a * 10 ^ n⌋ : ℚ) + 1 := Int.lt_floor_add_one _
  refine ⟨((⌊a * 10 ^ n⌋ + 1 : ℤ) : ℚ) / 10 ^ n, ⟨n, _, rfl⟩, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]; push_cast; exact hlt
  · rw [div_lt_iff₀ hp]; push_cast; nlinarith

/-- The integers of `(a, b)` are finitely many. -/
theorem ints_finite (a b : ℚ) : {q : ℚ | a < q ∧ q < b ∧ ∃ z : ℤ, q = z}.Finite := by
  refine ((Set.finite_Icc ⌊a⌋ ⌈b⌉).image (fun z : ℤ => (z : ℚ))).subset ?_
  rintro q ⟨haq, hqb, z, rfl⟩
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · simpa using Int.floor_mono haq.le
  · simpa using Int.ceil_mono hqb.le

/-- **Decimal band.** The non-integer decimals of a nonempty open interval
are infinitely many. -/
theorem decimal_band_infinite {a b : ℚ} (h : a < b) :
    {q : ℚ | a < q ∧ q < b ∧ IsDecimal q ∧ ¬ ∃ z : ℤ, q = z}.Infinite := by
  obtain ⟨d, hd, had, hdm⟩ := exists_decimal_btwn (show a < (a + b) / 2 by linarith)
  obtain ⟨M, hM⟩ := exists_small ((b - a) / 2) (by linarith)
  let f : ℕ → ℚ := fun j => d + 1 / 10 ^ (M + j)
  have hinj : Function.Injective f := by
    intro i j hij
    have : (1 : ℚ) / 10 ^ (M + i) = 1 / 10 ^ (M + j) := add_left_cancel hij
    have := inv_pow_injective this
    omega
  have hA : {q : ℚ | a < q ∧ q < b ∧ IsDecimal q}.Infinite := by
    refine Set.infinite_of_injective_forall_mem hinj fun j => ?_
    have hpos : (0 : ℚ) < 1 / 10 ^ (M + j) := by positivity
    have hle := inv_pow_le (K := ℚ) M j
    exact ⟨by simp only [f]; linarith, by simp only [f]; linarith,
      isDecimal_add hd (isDecimal_inv_pow _)⟩
  refine (hA.diff (ints_finite a b)).mono ?_
  rintro q ⟨⟨haq, hqb, hq⟩, hnot⟩
  exact ⟨haq, hqb, hq, fun hz => hnot ⟨haq, hqb, hz⟩⟩

/-- `1 / (3 · 10^n)` added to a decimal is not a decimal. -/
theorem not_isDecimal_add_third {d : ℚ} (hd : IsDecimal d) (n : ℕ) :
    ¬ IsDecimal (d + 1 / (3 * 10 ^ n)) := by
  rintro ⟨k, m, hm⟩
  obtain ⟨k', m', rfl⟩ := hd
  have h10 : ∀ j : ℕ, (0 : ℚ) < 10 ^ j := fun j => by positivity
  have key : ((10 ^ (k + k') : ℤ) : ℚ) = ((3 * 10 ^ n * (m * 10 ^ k' - m' * 10 ^ k) : ℤ) : ℚ) := by
    push_cast
    rw [pow_add]
    field_simp at hm
    linarith
  have hz : (10 : ℤ) ^ (k + k') = 3 * 10 ^ n * (m * 10 ^ k' - m' * 10 ^ k) := by exact_mod_cast key
  have h3 : (3 : ℤ) ∣ 10 ^ (k + k') := ⟨10 ^ n * (m * 10 ^ k' - m' * 10 ^ k), by rw [hz]; ring⟩
  have := Int.prime_three.dvd_of_dvd_pow h3
  omega

/-- **Rational band.** The rationals of a nonempty open interval that are
not decimals are infinitely many. -/
theorem rational_band_infinite {a b : ℚ} (h : a < b) :
    {q : ℚ | a < q ∧ q < b ∧ ¬ IsDecimal q}.Infinite := by
  obtain ⟨d, hd, had, hdm⟩ := exists_decimal_btwn (show a < (a + b) / 2 by linarith)
  obtain ⟨M, hM⟩ := exists_small ((b - a) / 2) (by linarith)
  let f : ℕ → ℚ := fun j => d + 1 / (3 * 10 ^ (M + j))
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : (1 : ℚ) / (3 * 10 ^ (M + i)) = 1 / (3 * 10 ^ (M + j)) := add_left_cancel hij
    have h2 : (1 : ℚ) / 10 ^ (M + i) = 1 / 10 ^ (M + j) := by
      have := congrArg (· * 3) h1
      simp only at this
      field_simp at this ⊢
      linarith
    have := inv_pow_injective h2
    omega
  refine Set.infinite_of_injective_forall_mem hinj fun j => ?_
  have hpos : (0 : ℚ) < 1 / (3 * 10 ^ (M + j)) := by positivity
  have h3 : (1 : ℚ) / (3 * 10 ^ (M + j)) ≤ 1 / 10 ^ (M + j) :=
    one_div_le_one_div_of_le (by positivity) (by linarith [show (0 : ℚ) < 10 ^ (M + j) from by positivity])
  have hle := inv_pow_le (K := ℚ) M j
  exact ⟨by simp only [f]; linarith, by simp only [f]; linarith, not_isDecimal_add_third hd _⟩

/-- **Real band.** The irrationals of a nonempty open interval are
infinitely many. -/
theorem real_band_infinite {a b : ℝ} (h : a < b) :
    {x : ℝ | a < x ∧ x < b ∧ Irrational x}.Infinite := by
  obtain ⟨r, hr, har, hrm⟩ := exists_irrational_btwn (show a < (a + b) / 2 by linarith)
  obtain ⟨M, hM⟩ := exists_small ((b - a) / 2) (by linarith)
  let f : ℕ → ℝ := fun j => r + ((1 / 10 ^ (M + j) : ℚ) : ℝ)
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : ((1 / 10 ^ (M + i) : ℚ) : ℝ) = ((1 / 10 ^ (M + j) : ℚ) : ℝ) := add_left_cancel hij
    have := inv_pow_injective (K := ℚ) (by exact_mod_cast h1)
    omega
  refine Set.infinite_of_injective_forall_mem hinj fun j => ?_
  have hpos : (0 : ℝ) < 1 / 10 ^ (M + j) := by positivity
  have hle := inv_pow_le (K := ℝ) M j
  refine ⟨?_, ?_, hr.add_ratCast _⟩ <;> simp only [f] <;> push_cast <;> linarith

end ContextCalculus.DataRangeDecimalBands
