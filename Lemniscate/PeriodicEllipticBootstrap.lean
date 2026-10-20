import Lemniscate.PeriodicH2Fourier

/-! A distributional fourth-order equation with L2 data of order at most two
gains two weak derivatives. The estimate treats every Fourier frequency,
including zero, and does not assume regularity of the unknown. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

theorem norm_second_of_fourth_identity (a z u v w : ℂ)
    (heq : a^4*z = a^2*u+a*v+w) :
    ‖a^2*z‖ ≤ ‖z‖+‖u‖+‖v‖+‖w‖ := by
  simp only [norm_mul, norm_pow]
  by_cases ha : ‖a‖ ≤ 1
  · have ha₂ : ‖a‖^2 ≤ 1 := by nlinarith [norm_nonneg a]
    have hz := mul_le_mul_of_nonneg_right ha₂ (norm_nonneg z)
    nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg w]
  · have ha₁ : 1 ≤ ‖a‖ := le_of_lt (lt_of_not_ge ha)
    have ha₂ : 1 ≤ ‖a‖^2 := by nlinarith
    have ha₃ : ‖a‖ ≤ ‖a‖^2 := by nlinarith
    have hp : 0 < ‖a‖^2 := by positivity
    have hn : ‖a‖^4*‖z‖ ≤ ‖a‖^2*‖u‖+‖a‖*‖v‖+‖w‖ := by
      calc
        _ = ‖a^4*z‖ := by rw [norm_mul, norm_pow]
        _ = ‖a^2*u+a*v+w‖ := congrArg norm heq
        _ ≤ ‖a^2*u‖+‖a*v‖+‖w‖ := norm_add₃_le
        _ = _ := by rw [norm_mul, norm_pow, norm_mul]
    have hb : ‖a‖^4*‖z‖ ≤ ‖a‖^2*(‖u‖+‖v‖+‖w‖) := by
      nlinarith [mul_le_mul_of_nonneg_right ha₃ (norm_nonneg v),
        mul_le_mul_of_nonneg_right ha₂ (norm_nonneg w)]
    have hc : ‖a‖^2*‖z‖ ≤ ‖u‖+‖v‖+‖w‖ := by
      apply (mul_le_mul_iff_right₀ hp).mp
      nlinarith [hb]
    linarith [norm_nonneg z]

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourier_mem_l2 (f : CircleL2 T) :
    Memℓp (fun n : ℤ => fourierCoeff f n) 2 := by
  have heq : (fun n : ℤ => fourierCoeff f n) =
      ((fourierBasis (T := T)).repr f : ℤ → ℂ) := by
    funext n
    exact (fourierBasis_repr f n).symm
  rw [heq]
  exact lp.memℓp ((fourierBasis (T := T)).repr f)

theorem circle_h2_of_fourth_distribution (f u v w : CircleL2 T)
    (heq : ∀ n : ℤ, (circleFrequencyFactor T n)^4*fourierCoeff f n =
      (circleFrequencyFactor T n)^2*fourierCoeff u n+
        circleFrequencyFactor T n*fourierCoeff v n+fourierCoeff w n) :
    InCircleH2 T f := by
  apply (circle_h2_iff_second_coefficients T f).mpr
  apply (((circle_fourier_mem_l2 T f).norm.add (circle_fourier_mem_l2 T u).norm).add
    (circle_fourier_mem_l2 T v).norm |>.add (circle_fourier_mem_l2 T w).norm).mono
  intro n
  exact norm_second_of_fourth_identity _ _ _ _ _ (heq n)

end Lemniscate
