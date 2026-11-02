import Lemniscate.PeriodicBlochHighFrequency

/-! Only a coarse fourth-moment lower bound is needed to absorb the
high-frequency L2 norm in the even-sector energy estimate. -/
namespace Lemniscate
open Complex MeasureTheory
variable (T : ℝ) [Fact (0 < T)]

theorem circle_high_fourth_weight_lower (f : circleH4Domain T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (f:CircleL2 T) n = 0) :
    4*‖(f:CircleL2 T)‖^2 ≤ ∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (f:CircleL2 T) n‖^2 := by
  have hp (n : ℤ) : 4*‖fourierCoeff (f:CircleL2 T) n‖^2 ≤
      (n:ℝ)^4*‖fourierCoeff (f:CircleL2 T) n‖^2 := by
    by_cases hn : |(n:ℝ)| < 32
    · rw [hf n hn,norm_zero]
      norm_num
    · have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) (le_of_not_gt hn) 4
      have heq : |(n:ℝ)|^4 = (n:ℝ)^4 := by
        calc
          _ = (|(n:ℝ)|^2)^2 := by ring
          _ = ((n:ℝ)^2)^2 := by rw [sq_abs]
          _ = _ := by ring
      rw [heq] at h
      have hn4 : (4:ℝ) ≤ (n:ℝ)^4 := by linarith only [h]
      exact mul_le_mul_of_nonneg_right hn4 (sq_nonneg _)
  have hs := (circle_fourier_square_summable T (f:CircleL2 T)).mul_left (4:ℝ)
  have h := hs.tsum_le_tsum hp (circle_fourier_fourth_weight_summable T f)
  simpa only [tsum_mul_left,← circle_norm_sq_fourier] using h

end Lemniscate
