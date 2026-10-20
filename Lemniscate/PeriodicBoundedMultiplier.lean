import Lemniscate.PeriodicAdjointRegularity

/-! Bounded Fourier multipliers on the actual periodic L2 space. The symbol
acts on the complete Hilbert basis, and the bound is an operator norm bound. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

theorem circle_multiplier_coefficients_mem_l2 (m : ℤ → ℂ) (C : ℝ)
    (hm : ∀ n, ‖m n‖ ≤ C) (f : CircleL2 T) :
    Memℓp (fun n => m n*fourierCoeff f n) 2 := by
  apply ((circle_fourier_mem_l2 T f).norm.const_mul C).mono
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)

noncomputable def circleMultiplierValue (m : ℤ → ℂ) (C : ℝ)
    (hm : ∀ n, ‖m n‖ ≤ C) (f : CircleL2 T) : CircleL2 T :=
  (fourierBasis (T := T)).repr.symm
    ⟨fun n => m n*fourierCoeff f n, circle_multiplier_coefficients_mem_l2 T m C hm f⟩

theorem circle_multiplier_value_fourier (m : ℤ → ℂ) (C : ℝ)
    (hm : ∀ n, ‖m n‖ ≤ C) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleMultiplierValue T m C hm f) n = m n*fourierCoeff f n := by
  rw [← fourierBasis_repr]
  change ((fourierBasis (T := T)).repr ((fourierBasis (T := T)).repr.symm _)) n = _
  rw [LinearIsometryEquiv.apply_symm_apply]

theorem circle_multiplier_value_norm_le (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) (f : CircleL2 T) :
    ‖circleMultiplierValue T m C hm f‖ ≤ C*‖f‖ := by
  calc
    _ = ‖(fourierBasis (T := T)).repr (circleMultiplierValue T m C hm f)‖ :=
      ((fourierBasis (T := T)).repr.norm_map _).symm
    _ ≤ ‖(fourierBasis (T := T)).repr ((C:ℂ) • f)‖ := by
      apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
      intro n
      rw [fourierBasis_repr, fourierBasis_repr, circle_multiplier_value_fourier,
        circle_fourierCoeff_smul]
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)
    _ = C*‖f‖ := by
      rw [(fourierBasis (T := T)).repr.norm_map, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hC]

noncomputable def circleBoundedMultiplier (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) : CircleL2 T →L[ℂ] CircleL2 T :=
  LinearMap.mkContinuous
    { toFun := circleMultiplierValue T m C hm
      map_add' := by
        intro f g
        apply circle_fourier_ext T
        intro n
        simp only [circle_multiplier_value_fourier, circle_fourierCoeff_add]
        ring
      map_smul' := by
        intro c f
        apply circle_fourier_ext T
        intro n
        simp only [RingHom.id_apply, circle_multiplier_value_fourier, circle_fourierCoeff_smul]
        ring }
    C (circle_multiplier_value_norm_le T m C hC hm)

theorem circle_bounded_multiplier_fourier (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (circleBoundedMultiplier T m C hC hm f) n = m n*fourierCoeff f n :=
  circle_multiplier_value_fourier T m C hm f n

theorem circle_bounded_multiplier_norm_le (m : ℤ → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) :
    ‖circleBoundedMultiplier T m C hC hm‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound (circleBoundedMultiplier T m C hC hm) hC
  intro f
  change ‖circleMultiplierValue T m C hm f‖ ≤ C*‖f‖
  exact circle_multiplier_value_norm_le T m C hC hm f

end Lemniscate
