import Lemniscate.IntervalSoundness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

/-! The actual coarse nome bounds, proved from Mathlib's theorems about pi
and the exponential series with a remainder bound. No numerical oracle. -/
namespace Lemniscate.CoarseArithmetic
open Finset

theorem exp_pi_quarter_lower : (109661/50000:ℝ) ≤ Real.exp (Real.pi/4) := by
  have he := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 31415/40000) 9
  have hp : (31415/40000:ℝ) ≤ Real.pi/4 := by linarith [Real.pi_gt_d4]
  apply le_trans _ (Real.exp_le_exp.mpr hp)
  apply le_trans _ he
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_pi_quarter_upper : Real.exp (Real.pi/4) ≤ (21933/10000:ℝ) := by
  have he := Real.exp_bound' (by norm_num : (0:ℝ) ≤ 3927/5000)
    (by norm_num : (3927/5000:ℝ) ≤ 1) (n := 9) (by decide)
  have hp : Real.pi/4 ≤ (3927/5000:ℝ) := by linarith [Real.pi_lt_d4]
  apply le_trans (Real.exp_le_exp.mpr hp)
  apply le_trans he
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem coarse_nome_bounds : Contains ⟨qlo,qhi⟩ (Real.exp (-Real.pi)) := by
  have heq : Real.exp Real.pi = (Real.exp (Real.pi/4))^4 := by
    convert! Real.exp_nat_mul (Real.pi/4) 4 using 1 <;> congr 1 <;> norm_num <;> ring
  have hl : (109661/50000:ℝ)^4 ≤ Real.exp Real.pi := by
    rw [heq]
    exact pow_le_pow_left₀ (by norm_num) exp_pi_quarter_lower 4
  have hu : Real.exp Real.pi ≤ (21933/10000:ℝ)^4 := by
    rw [heq]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_pi_quarter_upper 4
  have hp := Real.exp_pos Real.pi
  rw [Real.exp_neg]
  constructor
  · change (qlo:ℝ) ≤ (Real.exp Real.pi)⁻¹
    simpa only [one_div] using
      (calc
        (qlo:ℝ) ≤ 1/(21933/10000:ℝ)^4 := by norm_num [qlo]
        _ ≤ 1/Real.exp Real.pi := one_div_le_one_div_of_le hp hu)
  · change (Real.exp Real.pi)⁻¹ ≤ (qhi:ℝ)
    simpa only [one_div] using
      (calc
        1/Real.exp Real.pi ≤ 1/(109661/50000:ℝ)^4 :=
          one_div_le_one_div_of_le (by norm_num) hl
        _ ≤ (qhi:ℝ) := by norm_num [qhi])

end Lemniscate.CoarseArithmetic
