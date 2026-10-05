import Mathlib.Data.Int.Basic

/-!
Exact integer thresholds for comparisons with a rational numerator/denominator.
The denominator must be positive. Negative numerators use Euclidean division,
so these statements cover negative fractional thresholds as well as positives.
These are arithmetic lemmas, not a certificate of concrete-rule admission.
-/
namespace ContextCalculus.SWRLIntegerThresholds

def ceiling (numerator denominator : Int) : Int :=
  -((-numerator) / denominator)

theorem ceiling_matches_euclidean_implementation (numerator denominator : Int)
    (positive : 0 < denominator) :
    ceiling numerator denominator =
      if numerator % denominator = 0 then numerator / denominator
      else numerator / denominator + 1 := by
  unfold ceiling
  rw [Int.neg_ediv]
  have sign : denominator.sign = 1 := Int.sign_eq_one_of_pos positive
  by_cases divides : denominator ∣ numerator
  · have zero := Int.dvd_iff_emod_eq_zero.mp divides
    simp [divides, zero]
  · have nonzero : numerator % denominator ≠ 0 := by
      intro zero
      exact divides (Int.dvd_iff_emod_eq_zero.mpr zero)
    simp only [divides, nonzero, if_false, sign]
    omega

theorem integer_le_rational_iff (value numerator denominator : Int)
    (positive : 0 < denominator) :
    value * denominator ≤ numerator ↔ value ≤ numerator / denominator := by
  exact (Int.le_ediv_iff_mul_le positive).symm

theorem integer_gt_rational_iff (value numerator denominator : Int)
    (positive : 0 < denominator) :
    numerator < value * denominator ↔ numerator / denominator + 1 ≤ value := by
  rw [← Int.ediv_lt_iff_lt_mul positive]
  omega

theorem integer_ge_rational_iff (value numerator denominator : Int)
    (positive : 0 < denominator) :
    numerator ≤ value * denominator ↔ ceiling numerator denominator ≤ value := by
  have h := integer_le_rational_iff (-value) (-numerator) denominator positive
  simp only [Int.neg_mul] at h
  unfold ceiling
  omega

theorem integer_lt_rational_iff (value numerator denominator : Int)
    (positive : 0 < denominator) :
    value * denominator < numerator ↔ value ≤ ceiling numerator denominator - 1 := by
  have h := integer_ge_rational_iff value numerator denominator positive
  omega

#print axioms integer_le_rational_iff
#print axioms ceiling_matches_euclidean_implementation
#print axioms integer_gt_rational_iff
#print axioms integer_ge_rational_iff
#print axioms integer_lt_rational_iff
end ContextCalculus.SWRLIntegerThresholds
