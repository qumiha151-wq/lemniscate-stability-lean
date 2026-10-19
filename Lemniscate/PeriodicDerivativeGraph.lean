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

theorem circle_first_derivative_norm_sq_le (f u g : CircleL2 T)
    (hfu : HasWeakCircleDeriv T f u) (hug : HasWeakCircleDeriv T u g) :
    ‖u‖^2 ≤ ‖f‖^2+‖g‖^2 := by
  have hf := circle_fourier_square_summable T f
  have hg := circle_fourier_square_summable T g
  have hu := circle_fourier_square_summable T u
  rw [circle_norm_sq_fourier T u, circle_norm_sq_fourier T f, circle_norm_sq_fourier T g,
    ← hf.tsum_add hg]
  apply hu.tsum_le_tsum _ (hf.add hg)
  intro n
  rw [fourier_of_weak_circle_deriv T f u hfu,
    fourier_of_weak_circle_second T f g (weak_circle_second_of_deriv_chain T f u g hfu hug),
    ← circle_frequency_factor_sq]
  exact norm_first_multiplier_bound _ _

theorem circle_first_derivative_norm_le (f u g : CircleL2 T)
    (hfu : HasWeakCircleDeriv T f u) (hug : HasWeakCircleDeriv T u g) :
    ‖u‖ ≤ ‖f‖+‖g‖ := by
  have h := circle_first_derivative_norm_sq_le T f u g hfu hug
  nlinarith [norm_nonneg f, norm_nonneg u, norm_nonneg g,
    mul_nonneg (norm_nonneg f) (norm_nonneg g)]

theorem circle_first_derivative_tendsto {ι : Type*} {l : Filter ι}
    (F U G : ι → CircleL2 T) (f u g : CircleL2 T)
    (hFU : ∀ i, HasWeakCircleDeriv T (F i) (U i))
    (hUG : ∀ i, HasWeakCircleDeriv T (U i) (G i))
    (hfu : HasWeakCircleDeriv T f u) (hug : HasWeakCircleDeriv T u g)
    (hF : Tendsto F l (𝓝 f)) (hG : Tendsto G l (𝓝 g)) :
    Tendsto U l (𝓝 u) := by
  have hbound (i : ι) : ‖U i-u‖ ≤ ‖F i-f‖+‖G i-g‖ :=
    circle_first_derivative_norm_le T (F i-f) (U i-u) (G i-g)
      (weak_circle_deriv_sub T _ _ _ _ (hFU i) hfu)
      (weak_circle_deriv_sub T _ _ _ _ (hUG i) hug)
  have hn : Tendsto (fun i => ‖F i-f‖+‖G i-g‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_add] using
      ((hF.sub_const f).norm.add (hG.sub_const g).norm)
  have hz : Tendsto (fun i => U i-u) l (𝓝 0) := squeeze_zero_norm hbound hn
  simpa only [sub_add_cancel, zero_add] using hz.add_const u

end Lemniscate
