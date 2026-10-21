import Lemniscate.HigherGeometricMoments
import Lemniscate.SineArithmetic
import Lemniscate.OddPositivity
import Mathlib.Tactic.IntervalCases

/-! Soundness of the rational geometric moments and all their shifted tails,
through degree six. The tail is the full convergent series. -/
namespace Lemniscate.CoarseArithmetic

theorem moment_sound (p : ℕ) (hp : p ≤ 6) (z : ℚ) (hz : ‖(z:ℝ)‖ < 1) :
    HasSum (fun n : ℕ => (n:ℝ)^p*(z:ℝ)^n) (moment p z:ℝ) := by
  interval_cases p
  · simpa [moment] using hasSum_geometric_moment_zero (z:ℝ) hz
  · simpa [moment] using hasSum_geometric_moment_one (z:ℝ) hz
  · simpa [moment] using hasSum_geometric_moment_two (z:ℝ) hz
  · simpa [moment] using hasSum_geometric_moment_three (z:ℝ) hz
  · simpa [moment] using hasSum_geometric_moment_four (z:ℝ) hz
  · simpa [moment] using hasSum_geometric_moment_five (z:ℝ) hz
  · simpa [moment] using hasSum_geometric_moment_six (z:ℝ) hz

theorem moment_tail_sound (p : ℕ) (hp : p ≤ 6) (z : ℚ)
    (hz : ‖(z:ℝ)‖ < 1) (L : ℕ) :
    HasSum (fun n : ℕ => ((n+L:ℕ):ℝ)^p*(z:ℝ)^(n+L)) (momentTail p z L:ℝ) := by
  have ht := (hasSum_nat_add_iff' L).mpr (moment_sound p hp z hz)
  simpa only [momentTail, Rat.cast_sub, OddArithmetic.sumTo_eq_sum_range,
    Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] using ht

end Lemniscate.CoarseArithmetic
