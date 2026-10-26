import Lemniscate.PeriodicIntegrationByParts

/-! The first derivative is controlled by the zeroth and second derivatives.
Consequently convergence of the second-derivative graph also gives convergence
of the first derivative, without assuming it separately. -/
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped ENNReal Topology

variable (T : ℝ) [Fact (0 < T)]

theorem circle_norm_sq_fourier (f : CircleL2 T) :
    ‖f‖^2 = ∑' n : ℤ, ‖fourierCoeff f n‖^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    ((fourierBasis (T := T)).repr f)
  simpa [Real.rpow_two, fourierBasis_repr] using h

theorem weak_circle_deriv_sub (f u g v : CircleL2 T)
    (hf : HasWeakCircleDeriv T f u) (hg : HasWeakCircleDeriv T g v) :
    HasWeakCircleDeriv T (f-g) (u-v) := by
  intro φ φ₁ hφ
  rw [inner_sub_left, inner_sub_left, hf φ φ₁ hφ, hg φ φ₁ hφ]
  ring

theorem circle_weak_derivative_norm_sq_product (f f₁ f₂ : CircleL2 T)
    (hf : HasWeakCircleDeriv T f f₁) (hf₁ : HasWeakCircleDeriv T f₁ f₂) :
    ‖f₁‖^2 ≤ ‖f‖*‖f₂‖ := by
  have he := circle_weak_integration_by_parts T f f₁ f₁ f₂ hf hf₁
  calc
    ‖f₁‖^2 = (inner ℂ f₁ f₁).re := norm_sq_eq_re_inner (𝕜 := ℂ) f₁
    _ = (-inner ℂ f f₂).re := congrArg Complex.re he
    _ ≤ ‖-inner ℂ f f₂‖ := Complex.re_le_norm _
    _ = ‖inner ℂ f f₂‖ := norm_neg _
    _ ≤ ‖f‖*‖f₂‖ := norm_inner_le_norm _ _

theorem circle_first_derivative_tendsto {ι : Type*} {l : Filter ι}
    (F U G : ι → CircleL2 T) (f u g : CircleL2 T)
    (hFU : ∀ i, HasWeakCircleDeriv T (F i) (U i))
    (hUG : ∀ i, HasWeakCircleDeriv T (U i) (G i))
    (hfu : HasWeakCircleDeriv T f u) (hug : HasWeakCircleDeriv T u g)
    (hF : Tendsto F l (𝓝 f)) (hG : Tendsto G l (𝓝 g)) :
    Tendsto U l (𝓝 u) := by
  have hbound (i : ι) : ‖U i-u‖ ≤ ‖F i-f‖+‖G i-g‖ := by
    have h := circle_weak_derivative_norm_sq_product T (F i-f) (U i-u) (G i-g)
      (weak_circle_deriv_sub T _ _ _ _ (hFU i) hfu)
      (weak_circle_deriv_sub T _ _ _ _ (hUG i) hug)
    nlinarith [norm_nonneg (F i-f), norm_nonneg (U i-u), norm_nonneg (G i-g),
      mul_nonneg (norm_nonneg (F i-f)) (norm_nonneg (G i-g))]
  have hn : Tendsto (fun i => ‖F i-f‖+‖G i-g‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_add] using
      ((hF.sub_const f).norm.add (hG.sub_const g).norm)
  have hz : Tendsto (fun i => U i-u) l (𝓝 0) := squeeze_zero_norm hbound hn
  simpa only [sub_add_cancel, zero_add] using hz.add_const u

end Lemniscate
