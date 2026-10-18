import Lemniscate.PeriodicDerivativeChain

/-! Characterize periodic H2, defined by successive L2 weak derivatives,
by the complete Fourier sequence with the actual circle-coordinate weight. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

theorem circle_frequency_factor_norm_sq (n : ℤ) :
    ‖circleFrequencyFactor T n‖^2 = (2*Real.pi/T*(n:ℝ))^2 := by
  simp only [circleFrequencyFactor, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, mul_pow, sq_abs]

theorem circle_h2_iff_second_coefficients (f : CircleL2 T) :
    InCircleH2 T f ↔
      Memℓp (fun n : ℤ => (circleFrequencyFactor T n)^2 * fourierCoeff f n) 2 := by
  rw [circle_h2_iff_weak_second]
  constructor
  · rintro ⟨g, hfg⟩
    have heq : (fun n : ℤ => (circleFrequencyFactor T n)^2 * fourierCoeff f n) =
        (fun n : ℤ => ((fourierBasis (T := T)).repr g) n) := by
      funext n
      rw [fourierBasis_repr, fourier_of_weak_circle_second T f g hfg,
        ← circle_frequency_factor_sq]
    rw [heq]
    exact lp.memℓp ((fourierBasis (T := T)).repr g)
  · intro h
    let g : CircleL2 T := (fourierBasis (T := T)).repr.symm
      ⟨fun n : ℤ => (circleFrequencyFactor T n)^2 * fourierCoeff f n, h⟩
    refine ⟨g, weak_circle_second_of_fourier T f g ?_⟩
    intro n
    rw [← circle_frequency_factor_sq, ← fourierBasis_repr]
    change ((fourierBasis (T := T)).repr
      ((fourierBasis (T := T)).repr.symm _)) n = _
    rw [LinearIsometryEquiv.apply_symm_apply]

theorem circle_second_coefficients_iff_weighted (f : CircleL2 T) :
    Memℓp (fun n : ℤ => (circleFrequencyFactor T n)^2 * fourierCoeff f n) 2 ↔
      Summable (fun n : ℤ =>
        ((1+(2*Real.pi/T*(n:ℝ))^2)*‖fourierCoeff f n‖)^2) := by
  have hn (n : ℤ) : ‖(circleFrequencyFactor T n)^2 * fourierCoeff f n‖^2 =
      ((2*Real.pi/T*(n:ℝ))^2 * ‖fourierCoeff f n‖)^2 := by
    rw [norm_mul, norm_pow, circle_frequency_factor_norm_sq]
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hn]
  constructor
  · intro hs
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
      (((circle_fourier_square_summable T f).add hs).mul_left 2)
    intro n
    nlinarith [sq_nonneg
      (‖fourierCoeff f n‖ - (2*Real.pi/T*(n:ℝ))^2*‖fourierCoeff f n‖)]
  · intro hs
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
    intro n
    apply pow_le_pow_left₀ (by positivity) _ 2
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)

theorem circle_h2_iff_weighted_fourier (f : CircleL2 T) :
    InCircleH2 T f ↔ Summable (fun n : ℤ =>
      ((1+(2*Real.pi/T*(n:ℝ))^2)*‖fourierCoeff f n‖)^2) := by
  rw [circle_h2_iff_second_coefficients, circle_second_coefficients_iff_weighted]

end Lemniscate
