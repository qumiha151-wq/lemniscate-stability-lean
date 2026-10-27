import Lemniscate.IntervalSoundness
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

/-! The nome enclosure needed for the fixed rational adjoint trial.
Only the proved twenty-digit bounds for pi and a 26-term exponential sum are used. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def nomeLower : ℚ := 43213918263772249774 / 10^21
def nomeUpper : ℚ := 43213918263772249775 / 10^21

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem refined_nome_bounds : Contains ⟨nomeLower,nomeUpper⟩ (Real.exp (-Real.pi)) := by
  have hlow : (219328005073801545655832/10^23:ℝ) ≤ Real.exp (Real.pi/4) := by
    have he := Real.sum_le_exp_of_nonneg
      (by norm_num : (0:ℝ) ≤ 314159265358979323846/(4*10^20)) 26
    have hp : (314159265358979323846/(4*10^20):ℝ) ≤ Real.pi/4 := by
      linarith [Real.pi_gt_d20]
    apply le_trans _ (Real.exp_le_exp.mpr hp)
    apply le_trans _ he
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hupp : Real.exp (Real.pi/4) ≤ (219328005073801545656381/10^23:ℝ) := by
    have he := Real.exp_bound'
      (by norm_num : (0:ℝ) ≤ 314159265358979323847/(4*10^20))
      (by norm_num : (314159265358979323847/(4*10^20):ℝ) ≤ 1)
      (n := 26) (by decide)
    have hp : Real.pi/4 ≤ (314159265358979323847/(4*10^20):ℝ) := by
      linarith [Real.pi_lt_d20]
    apply le_trans (Real.exp_le_exp.mpr hp)
    apply le_trans he
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have heq : Real.exp Real.pi = (Real.exp (Real.pi/4))^4 := by
    convert! Real.exp_nat_mul (Real.pi/4) 4 using 1 <;> congr 1 <;> norm_num <;> ring
  have hl : (219328005073801545655832/10^23:ℝ)^4 ≤ Real.exp Real.pi := by
    rw [heq]
    exact pow_le_pow_left₀ (by norm_num) hlow 4
  have hu : Real.exp Real.pi ≤ (219328005073801545656381/10^23:ℝ)^4 := by
    rw [heq]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hupp 4
  have hp := Real.exp_pos Real.pi
  rw [Real.exp_neg]
  constructor
  · change (nomeLower:ℝ) ≤ (Real.exp Real.pi)⁻¹
    simpa only [one_div] using
      (calc
        (nomeLower:ℝ) ≤ 1/(219328005073801545656381/10^23:ℝ)^4 := by norm_num [nomeLower]
        _ ≤ 1/Real.exp Real.pi := one_div_le_one_div_of_le hp hu)
  · change (Real.exp Real.pi)⁻¹ ≤ (nomeUpper:ℝ)
    simpa only [one_div] using
      (calc
        1/Real.exp Real.pi ≤ 1/(219328005073801545655832/10^23:ℝ)^4 :=
          one_div_le_one_div_of_le (by norm_num) hl
        _ ≤ (nomeUpper:ℝ) := by norm_num [nomeUpper])

end Lemniscate.CoarseArithmetic
