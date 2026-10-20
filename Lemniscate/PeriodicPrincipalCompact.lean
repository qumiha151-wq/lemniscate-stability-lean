import Lemniscate.PeriodicPrincipalResolvent
import Lemniscate.PeriodicCompactMultiplier
import Mathlib.Analysis.PSeries

/-! Compactness of the actual principal resolvent. The zero mode is handled
separately; every nonzero mode is dominated by a convergent fourth-power series. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_principal_symbol_norm_summable (r : ℝ) (hr : 0 < r) :
    Summable (fun n : ℤ => ‖circlePrincipalSymbol T r n‖) := by
  have hκ : 0 < 2*Real.pi/T := div_pos (mul_pos (by norm_num) Real.pi_pos) (Fact.out)
  have hp : Summable (fun n : ℤ => (4*(2*Real.pi/T)^4)⁻¹*(1/(n:ℝ)^4)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < (4:ℕ))).mul_left _
  have hz : Summable (fun n : ℤ => if n = 0 then r⁻¹ else 0) := by
    exact (hasSum_ite_eq 0 r⁻¹).summable
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (hz.add hp)
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [ite_true, Int.cast_zero, zero_pow (by decide : 4 ≠ 0), div_zero,
      mul_zero, add_zero] using circle_principal_symbol_bound T r hr 0
  · have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn
    have hd : 0 < 4*(2*Real.pi/T)^4*(n:ℝ)^4 := by positivity
    have hb := one_div_le_one_div_of_le hd
      (show 4*(2*Real.pi/T)^4*(n:ℝ)^4 ≤ r+4*(2*Real.pi/T)^4*(n:ℝ)^4 by linarith)
    rw [circlePrincipalSymbol, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (circle_principal_denominator_pos T r hr n), if_neg hn, zero_add]
    simpa only [one_div, mul_inv_rev, mul_comm] using hb

theorem circle_principal_resolvent_compact (r : ℝ) (hr : 0 < r) :
    IsCompactOperator (circlePrincipalResolvent T r hr) :=
  circle_bounded_multiplier_compact T (circlePrincipalSymbol T r) r⁻¹ (by positivity)
    (circle_principal_symbol_bound T r hr) (circle_principal_symbol_norm_summable T r hr)

end Lemniscate
