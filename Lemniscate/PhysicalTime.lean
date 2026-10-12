import Lemniscate.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The exact physical-time conversion in (1.8)--(1.10).
No existence or convergence of a flow is assumed or asserted here. -/
namespace Lemniscate

noncomputable def timeBase (a t : ℝ) : ℝ := 1+30*t/a^4
noncomputable def normalizedTime (a t : ℝ) : ℝ := (1/30:ℝ)*Real.log (timeBase a t)

theorem timeBase_pos (a t : ℝ) (ha : 0 < a) (ht : 0 ≤ t) : 0 < timeBase a t := by
  have hnonneg : 0 ≤ 30*t/a^4 := div_nonneg (by linarith) (le_of_lt (pow_pos ha 4))
  dsimp [timeBase]
  linarith

theorem physical_decay_identity (a t mu : ℝ) (ha : 0 < a) (ht : 0 ≤ t) :
    Real.exp (-mu*normalizedTime a t) = (timeBase a t)^(-mu/30) := by
  rw [Real.rpow_def_of_pos (timeBase_pos a t ha ht)]
  congr 1
  unfold normalizedTime
  ring

theorem timeBase_at_unit_scale (a t : ℝ) (ha : 0 < a) (ht : a^4 ≤ t) :
    31 ≤ timeBase a t := by
  have ha4 : 0 < a^4 := pow_pos ha 4
  have h : (30:ℝ) ≤ 30*t/a^4 := (le_div_iff₀ ha4).mpr (by nlinarith)
  dsimp [timeBase]
  linarith

theorem normalizedTime_at_unit_scale (a t : ℝ) (ha : 0 < a) (ht : a^4 ≤ t) :
    Real.log 31/30 ≤ normalizedTime a t := by
  have h := Real.log_le_log (by norm_num : (0:ℝ) < 31) (timeBase_at_unit_scale a t ha ht)
  unfold normalizedTime
  linarith

end Lemniscate
