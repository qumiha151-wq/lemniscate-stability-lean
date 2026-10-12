import Lemniscate.OddArithmetic
import Lemniscate.Bernstein
import Mathlib.Data.Rat.Cast.Order

/-! The computed odd-sector coefficients imply a bound at every real
parameter in [0, 1/2]. This connects exact arithmetic to Bernstein positivity.
The analytic interpretation as a Fourier row remains a separate obligation. -/
namespace Lemniscate.OddArithmetic
open Finset CoarseArithmetic

theorem sumTo_eq_sum_range (n : ℕ) (f : ℕ → ℚ) :
    sumTo n f = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simpa [sumTo, List.range_succ, List.map_append, List.sum_append,
      Finset.sum_range_succ] using congrArg (fun q : ℚ => q + f n) ih

theorem bernsteinSix_cast (p : Poly) (k : ℕ) :
    (bernsteinSix p k : ℝ) =
      bernsteinCoefficient 6 k (fun j => (coeff p j : ℝ)) := by
  rw [bernsteinSix, sumTo_eq_sum_range]
  simp only [bernsteinCoefficient, Rat.cast_sum, Rat.cast_div,
    Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro j hj
  ring

noncomputable def realRowPolynomial (n : ℤ) (α : ℝ) : ℝ :=
  ∑ j ∈ range 7, (coeff (rowPolynomial n) j : ℝ)*α^j

theorem odd_rows_positive_on_interval (i : Fin 12) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (1/2:ℝ) ≤ realRowPolynomial (lowIndex i) α := by
  apply degree_six_polynomial_lower_bound _ _ _ hα hα'
  intro k hk
  have hk' : k < 7 := Finset.mem_range.mp hk
  rw [← bernsteinSix_cast]
  have h := all_odd_bernstein_comparisons i ⟨k, hk'⟩
  have hr : ((1/2:ℚ):ℝ) ≤ (bernsteinSix (rowPolynomial (lowIndex i)) k : ℝ) :=
    Rat.cast_le.mpr (le_of_lt h)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hr
  exact hr

theorem odd_zero_rows_real (i : Fin 12) :
    (5:ℝ) < (coeff (rowPolynomial (lowIndex i)) 0 : ℝ) /
      (coeff (weight (lowIndex i)) 0 : ℝ) := by
  exact_mod_cast all_odd_zero_comparisons i

end Lemniscate.OddArithmetic
