import Lemniscate.ShortWeightedFourier
import Lemniscate.ShortSineSobolevTail

/-! Inverse-weight Fourier coordinates are genuine L2 contractions, and
their norms on finite sine trials are exact finite weighted sums. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ENNReal ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem short_inverse_fourier_norm_le (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (f : CircleL2 T) : ‖shortInverseWeightFourier T w hw f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖(fourierBasis (T := T)).repr f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      rw [short_inverse_weight_fourier_apply, fourierBasis_repr, norm_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (lt_of_lt_of_le zero_lt_one (hw n)).le)]
      have hi : (w n)⁻¹ ≤ 1 :=
        (inv_le_one₀ (lt_of_lt_of_le zero_lt_one (hw n))).mpr (hw n)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hi (norm_nonneg (fourierCoeff f n))
    _ = ‖f‖ := (fourierBasis (T := T)).repr.norm_map f

def shortInverseWeightFourierCLM (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n) :
    CircleL2 T →L[ℂ] ShortFourierHilbert :=
  LinearMap.mkContinuous
    { toFun := shortInverseWeightFourier T w hw
      map_add' := by
        intro f g
        apply lp.ext
        funext n
        change (((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff (f + g) n =
          (((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff f n +
            (((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff g n
        rw [circle_fourierCoeff_add, mul_add]
      map_smul' := by
        intro c f
        apply lp.ext
        funext n
        change (((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff (c • f) n =
          c * ((((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff f n)
        rw [circle_fourierCoeff_smul]
        ring }
    1 (by intro f; simpa only [one_mul] using! short_inverse_fourier_norm_le T w hw f)

@[simp] theorem short_inverse_fourier_clm_apply (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (f : CircleL2 T) :
    shortInverseWeightFourierCLM T w hw f = shortInverseWeightFourier T w hw f := rfl

theorem short_inverse_fourier_clm_norm_le (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n) :
    ‖shortInverseWeightFourierCLM T w hw‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0 : ℝ) ≤ 1)
  intro f
  simpa only [short_inverse_fourier_clm_apply, one_mul] using
    short_inverse_fourier_norm_le T w hw f

private theorem short_sine_trial_fourier {N : ℕ} (v : Fin N → ℂ) (n : ℤ) :
    fourierCoeff (circleSineTrialH4 T N v : CircleL2 T) n =
      ∑ j : Fin N, v j * fourierCoeff (circleEvenSineMode T j.val) n := by
  simp only [← fourierBasis_repr, HilbertBasis.repr_apply_apply, circleSineTrialH4,
    Submodule.coe_sum, Submodule.coe_smul_of_tower, inner_sum, inner_smul_right]
  simp only [circleSineH4, circleFourierH4, circleEvenSineMode, evenSineMode,
    Submodule.coe_smul_of_tower, Submodule.coe_sub]

private theorem short_inverse_sine_symbol (w : ℤ → ℝ) (hsym : ∀ n, w (-n) = w n)
    (j : ℕ) (n : ℤ) :
    (((w n)⁻¹ : ℝ) : ℂ) * fourierCoeff (circleEvenSineMode T j) n =
      (((w (2 * ((j + 1 : ℕ) : ℤ)))⁻¹ : ℝ) : ℂ) *
        fourierCoeff (circleEvenSineMode T j) n := by
  rw [circle_even_sine_mode_coeff]
  by_cases hp : n = 2 * ((j + 1 : ℕ) : ℤ)
  · subst n
    rfl
  by_cases hm : n = -(2 * ((j + 1 : ℕ) : ℤ))
  · subst n
    rw [hsym]
  · simp only [if_neg hp, if_neg hm, sub_self, mul_zero]

/-- Exact full-Fourier semantics for the inverse weighted norm of a finite
sine trial.  The weights are at least one and reflection invariant. -/
theorem short_inverse_sine_norm_sq (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n)
    (hsym : ∀ n, w (-n) = w n) {N : ℕ} (v : Fin N → ℂ) :
    ‖shortInverseWeightFourier T w hw (circleSineTrialH4 T N v : CircleL2 T)‖ ^ 2 =
      ∑ j : Fin N, (w (2 * ((j.val + 1 : ℕ) : ℤ)))⁻¹ ^ 2 * ‖v j‖ ^ 2 := by
  let v' : Fin N → ℂ := fun j =>
    (((w (2 * ((j.val + 1 : ℕ) : ℤ)))⁻¹ : ℝ) : ℂ) * v j
  have he : shortInverseWeightFourier T w hw (circleSineTrialH4 T N v : CircleL2 T) =
      (fourierBasis (T := T)).repr (circleSineTrialH4 T N v' : CircleL2 T) := by
    apply lp.ext
    funext n
    rw [short_inverse_weight_fourier_apply, fourierBasis_repr,
      short_sine_trial_fourier, short_sine_trial_fourier, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      _ = v j * ((((w n)⁻¹ : ℝ) : ℂ) *
          fourierCoeff (circleEvenSineMode T j.val) n) := by ring
      _ = v j * ((((w (2 * ((j.val + 1 : ℕ) : ℤ)))⁻¹ : ℝ) : ℂ) *
          fourierCoeff (circleEvenSineMode T j.val) n) := by
        rw [short_inverse_sine_symbol T w hsym]
      _ = _ := by dsimp only [v']; ring
  rw [he, (fourierBasis (T := T)).repr.norm_map, (short_sine_trial_norms_sq T v').1]
  apply Finset.sum_congr rfl
  intro j _
  simp only [v', norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Lemniscate
