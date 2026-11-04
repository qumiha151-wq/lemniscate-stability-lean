import Lemniscate.PeriodicParabolicSpace
import Lemniscate.PeriodicSobolevFourierProjection
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Logic.Equiv.List
import Mathlib.Analysis.Real.Sqrt

/-! Spatial Fourier truncation of arbitrary L2 time forcing.
The squared pointwise error tends to zero and is bounded by 4*norm(F)^2.
Scalar dominated convergence and the actual L2 integral norm identify the
limit in time L2, without imposing continuity on the forcing.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

def circleTimeFourierProjection (I : Finset ℤ) : CircleTimeL2 T →L[ℂ] CircleTimeL2 T :=
  (circleFourierProjection T I).compLpL 2 (volume : Measure unitInterval)

theorem circle_time_fourier_projection_norm_le (I : Finset ℤ) :
    ‖circleTimeFourierProjection T I‖ ≤ 1 :=
  ((circleFourierProjection T I).norm_compLpL_le
    (p := 2) (μ := (volume : Measure unitInterval))).trans
      (circle_fourier_projection_norm_le T I)

private theorem circle_fourier_projection_sq_error_bound (I : Finset ℤ) (f : CircleL2 T) :
    ‖circleFourierProjection T I f-f‖^2 ≤ (4:ℝ)*‖f‖^2 := by
  let a : ℝ := ‖circleFourierProjection T I f-f‖
  let b : ℝ := ‖f‖
  have ha : (0:ℝ) ≤ a := norm_nonneg (circleFourierProjection T I f-f)
  have hb : (0:ℝ) ≤ b := norm_nonneg f
  have hP : ‖circleFourierProjection T I f‖ ≤ b := by
    simpa only [b,one_mul] using (circleFourierProjection T I).le_of_opNorm_le
      (circle_fourier_projection_norm_le T I) f
  have he : a ≤ (2:ℝ)*b := by
    calc
      a ≤ ‖circleFourierProjection T I f‖+b := norm_sub_le (circleFourierProjection T I f) f
      _ ≤ b+b := add_le_add hP (le_rfl : b ≤ b)
      _ = (2:ℝ)*b := by ring
  have htwo : (0:ℝ) ≤ (2:ℝ)*b := mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb
  have hs : a^2 ≤ ((2:ℝ)*b)^2 := (sq_le_sq₀ ha htwo).mpr he
  change a^2 ≤ (4:ℝ)*b^2
  calc
    a^2 ≤ ((2:ℝ)*b)^2 := hs
    _ = (4:ℝ)*b^2 := by ring

set_option maxHeartbeats 600000 in
/-- Spatial finite Fourier projections converge strongly for every time L2 forcing. -/
theorem circle_time_fourier_projection_tendsto (F : CircleTimeL2 T) :
    Tendsto (fun I : Finset ℤ => circleTimeFourierProjection T I F) atTop (𝓝 F) := by
  let e : Finset ℤ → unitInterval → ℝ :=
    fun I t => ‖circleFourierProjection T I (F t)-F t‖^2
  have herr (I : Finset ℤ) : MemLp
      (fun t : unitInterval => circleFourierProjection T I (F t)-F t) 2 volume :=
    ((circleFourierProjection T I).comp_memLp F).sub (Lp.memLp F)
  have heint (I : Finset ℤ) : Integrable (e I) volume :=
    (memLp_two_iff_integrable_sq_norm (herr I).aestronglyMeasurable).mp (herr I)
  have hFint : Integrable (fun t : unitInterval => ‖F t‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hbound (I : Finset ℤ) (t : unitInterval) : ‖e I t‖ ≤ (4:ℝ)*‖F t‖^2 := by
    dsimp only [e]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (‖circleFourierProjection T I (F t)-F t‖ : ℝ))]
    exact circle_fourier_projection_sq_error_bound T I (F t)
  have hpoint (t : unitInterval) : Tendsto (fun I : Finset ℤ => e I t) atTop (𝓝 0) := by
    simpa only [e,sub_self,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] using
      (((circle_fourier_projection_tendsto T (F t)).sub_const (F t)).norm.pow 2)
  have hint : Tendsto (fun I : Finset ℤ => ∫ t, e I t ∂volume) atTop (𝓝 (0:ℝ)) := by
    simpa only [integral_zero] using
      (tendsto_integral_filter_of_dominated_convergence
        (f := fun _ : unitInterval => (0:ℝ)) (fun t : unitInterval => 4*‖F t‖^2)
        (Eventually.of_forall fun I => (heint I).aestronglyMeasurable)
        (Eventually.of_forall fun I => Eventually.of_forall (hbound I))
        (hFint.const_mul 4) (Eventually.of_forall hpoint))
  have hnormsq (I : Finset ℤ) :
      ‖circleTimeFourierProjection T I F-F‖^2 = ∫ t, e I t ∂volume := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
      ← integral_re (L2.integrable_inner (𝕜 := ℂ)
        (circleTimeFourierProjection T I F-F) (circleTimeFourierProjection T I F-F))]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (circleTimeFourierProjection T I F) F,
      (circleFourierProjection T I).coeFn_compLpL
        (p := 2) (μ := (volume : Measure unitInterval)) F] with t ht hP
    rw [ht]
    simp only [Pi.sub_apply,circleTimeFourierProjection]
    rw [hP]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) (circleFourierProjection T I (F t)-F t)).symm
  have hsq : Tendsto
      (fun I : Finset ℤ => ‖circleTimeFourierProjection T I F-F‖^2) atTop (𝓝 (0:ℝ)) := by
    simpa only [hnormsq] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto (0:ℝ)).comp hsq

end Lemniscate
