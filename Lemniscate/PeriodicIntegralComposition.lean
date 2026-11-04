import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Linarith

/-! The square-integral estimate needed for the normal projection. -/
noncomputable section
namespace Lemniscate
open MeasureTheory Set

theorem periodic_integral_comp_square_le
    (L : ℝ) (hL : 0 < L) (f χ : ℝ → ℝ)
    (hf : Continuous f) (hfper : Function.Periodic f L)
    (hχ : ContDiff ℝ 1 χ) (hχend : χ L = χ 0+L)
    (hχlower : ∀ s ∈ Icc (0:ℝ) L, (1/4:ℝ) ≤ deriv χ s) :
    (∫ s in (0:ℝ)..L, (f (χ s))^2) ≤
      4*(∫ s in (0:ℝ)..L, (f s)^2) := by
  have hf₂ : Continuous (fun s => (f s)^2) := hf.pow 2
  have hc₂ : Continuous (fun s => (f (χ s))^2) := hf₂.comp hχ.continuous
  have hp₂ : Function.Periodic (fun s => (f s)^2) L := by
    intro s
    change (f (s+L))^2 = (f s)^2
    rw [hfper s]
  have hchange :
      (∫ s in (0:ℝ)..L, (f (χ s))^2*deriv χ s) =
        ∫ s in (0:ℝ)..L, (f s)^2 := by
    calc
      _ = ∫ s in χ 0..χ L, (f s)^2 := by
        simpa only [Function.comp_def] using
          (intervalIntegral.integral_comp_mul_deriv
            (a := 0) (b := L) (f := χ) (f' := deriv χ)
            (g := fun s => (f s)^2)
            (fun s _ => (hχ.differentiable_one s).hasDerivAt)
            hχ.continuous_deriv_one.continuousOn hf₂)
      _ = ∫ s in (0:ℝ)..L, (f s)^2 := by
        rw [hχend]
        simpa only [zero_add] using hp₂.intervalIntegral_add_eq (χ 0) 0
  calc
    _ ≤ ∫ s in (0:ℝ)..L, 4*((f (χ s))^2*deriv χ s) := by
      apply intervalIntegral.integral_mono_on hL.le
        (hc₂.intervalIntegrable 0 L)
        (((hc₂.mul hχ.continuous_deriv_one).const_mul 4).intervalIntegrable 0 L)
      intro s hs
      change (f (χ s))^2 ≤ 4*((f (χ s))^2*deriv χ s)
      nlinarith only [mul_nonneg (sq_nonneg (f (χ s)))
        (sub_nonneg.mpr (hχlower s hs))]
    _ = 4*(∫ s in (0:ℝ)..L, (f (χ s))^2*deriv χ s) :=
      intervalIntegral.integral_const_mul 4 _
    _ = _ := by rw [hchange]

end Lemniscate
