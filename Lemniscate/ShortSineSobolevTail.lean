import Lemniscate.ShortSobolevNorm
import Lemniscate.PeriodicSineDerivativeSeries

/-! The omitted sine coefficients control the actual V and H1 errors.
Only an absolute second-order coefficient moment is required. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem short_v_zero_mean (f : circleH4Domain T)
    (hf : fourierCoeff (f : CircleL2 T) 0 = 0) :
    shortVNorm T f = (shortAngularFrequency T)⁻¹ ^ 2 * ‖(circleH4Jet T f).second‖ := by
  apply (sq_eq_sq₀ (short_v_norm_nonneg T f)
    (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mp
  rw [short_v_norm_sq, hf, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
  ring

private theorem short_h1_le_derivative_sum (f : circleH4Domain T) :
    shortH1Norm T f ≤ ‖(f : CircleL2 T)‖ +
      (shortAngularFrequency T)⁻¹ * ‖(circleH4Jet T f).first‖ := by
  have hκ := short_angular_frequency_pos T
  have hs := short_h1_norm_sq T f
  have hp := mul_nonneg (norm_nonneg (f : CircleL2 T))
    (mul_nonneg (inv_nonneg.mpr hκ.le) (norm_nonneg (circleH4Jet T f).first))
  apply (sq_le_sq₀ (short_h1_norm_nonneg T f)
    (add_nonneg (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr hκ.le) (norm_nonneg _)))).mp
  nlinarith only [hs, hp]

private theorem short_sine_trial_mean_zero (N : ℕ) (v : Fin N → ℂ) :
    fourierCoeff (circleSineTrialH4 T N v : CircleL2 T) 0 = 0 := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  simp only [circleSineTrialH4, Submodule.coe_sum, Submodule.coe_smul_of_tower,
    inner_sum, inner_smul_right, ← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  change (∑ n : Fin N, v n * fourierCoeff (circleEvenSineMode T n.val) 0) = 0
  simp only [circle_even_sine_mode_coeff_zero, mul_zero, Finset.sum_const_zero]

private theorem short_angular_sine_derivative_tail (f : circleH4Domain T)
    (v : SineSequenceSpace) (hf : (f : CircleL2 T) = circleEvenSineSynthesis T v)
    (j : Fin 4)
    (hv : Summable (fun n : ℕ => ‖v n‖ * (2 * (n + 1 : ℕ) : ℝ) ^ (j.val + 1)))
    (N : ℕ) :
    (shortAngularFrequency T)⁻¹ ^ (j.val + 1) *
      ‖circleH4Derivative T j (f - circleSineTrialH4 T N (fun n => v n.val))‖ ≤
    ∑' n : ℕ, ‖v (n + N)‖ * (2 * (n + N + 1 : ℕ) : ℝ) ^ (j.val + 1) := by
  have hκ := short_angular_frequency_pos T
  have hv' : Summable (fun n : ℕ => ‖v n‖ *
      (2 * Real.pi / T * (2 * (n + 1 : ℕ) : ℝ)) ^ (j.val + 1)) := by
    simpa only [mul_pow, mul_left_comm, mul_assoc] using
      hv.mul_left ((2 * Real.pi / T) ^ (j.val + 1))
  have h := circle_sine_truncation_derivative_error T f v hf j hv' N
  have ht : (∑' n : ℕ, ‖v (n + N)‖ *
      (2 * Real.pi / T * (2 * (n + N + 1 : ℕ) : ℝ)) ^ (j.val + 1)) =
      (shortAngularFrequency T) ^ (j.val + 1) *
        ∑' n : ℕ, ‖v (n + N)‖ * (2 * (n + N + 1 : ℕ) : ℝ) ^ (j.val + 1) := by
    simp only [shortAngularFrequency, mul_pow, mul_left_comm ‖v _‖, mul_assoc,
      tsum_mul_left]
  rw [ht] at h
  have hh := mul_le_mul_of_nonneg_left h
    (pow_nonneg (inv_nonneg.mpr hκ.le) (j.val + 1))
  simpa only [inv_pow, ← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hκ.ne'), one_mul] using hh

/-- A single second-order absolute coefficient moment gives both angular
Sobolev tail bounds for the actual normalized sine truncation. -/
theorem short_sine_sobolev_tail (f : circleH4Domain T) (v : SineSequenceSpace)
    (hf : (f : CircleL2 T) = circleEvenSineSynthesis T v)
    (hv : Summable (fun n : ℕ => ‖v n‖ * (2 * (n + 1 : ℕ) : ℝ) ^ 2)) (N : ℕ) :
    shortVNorm T (f - circleSineTrialH4 T N (fun n => v n.val)) ≤
      ∑' n : ℕ, ‖v (n + N)‖ * (2 * (n + N + 1 : ℕ) : ℝ) ^ 2 ∧
    shortH1Norm T (f - circleSineTrialH4 T N (fun n => v n.val)) ≤
      ∑' n : ℕ, ‖v (n + N)‖ * (1 + (2 * (n + N + 1 : ℕ) : ℝ)) := by
  have hfreq (n : ℕ) : (2 : ℝ) ≤ (2 * (n + 1 : ℕ) : ℝ) := by
    norm_cast
    omega
  have hv₀ : Summable (fun n : ℕ => ‖v n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hv
    intro n
    have hh : (1 : ℝ) ≤ (2 * (n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hfreq n, sq_nonneg ((2 * (n + 1 : ℕ) : ℝ) - 1)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (norm_nonneg (v n))
  have hv₁ : Summable (fun n : ℕ => ‖v n‖ * (2 * (n + 1 : ℕ) : ℝ)) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (by positivity)) _ hv
    intro n
    have hh : (2 * (n + 1 : ℕ) : ℝ) ≤ (2 * (n + 1 : ℕ) : ℝ) ^ 2 := by
      nlinarith only [hfreq n, sq_nonneg ((2 * (n + 1 : ℕ) : ℝ) - 1)]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg _)
  let t : circleH4Domain T := f - circleSineTrialH4 T N (fun n => v n.val)
  have ht₀ : fourierCoeff (t : CircleL2 T) 0 = 0 := by
    have hf₀ : fourierCoeff (f : CircleL2 T) 0 = 0 := by
      rw [hf]
      exact circle_even_sine_coeff_zero T v
    have hp₀ : fourierCoeff
        (circleSineTrialH4 T N (fun n => v n.val) : CircleL2 T) 0 = 0 := by
      exact short_sine_trial_mean_zero T N _
    have hsub : fourierCoeff (t : CircleL2 T) 0 = fourierCoeff (f : CircleL2 T) 0 -
        fourierCoeff (circleSineTrialH4 T N (fun n => v n.val) : CircleL2 T) 0 := by
      simp only [t, Submodule.coe_sub, ← fourierBasis_repr,
        HilbertBasis.repr_apply_apply, inner_sub_right]
    rw [hsub, hf₀, hp₀, sub_self]
  have h₂ := short_angular_sine_derivative_tail T f v hf (1 : Fin 4) hv N
  have h₁ := short_angular_sine_derivative_tail T f v hf (0 : Fin 4)
    (by simpa only [Fin.val_zero, zero_add, pow_one] using hv₁) N
  simp only [Fin.val_zero, zero_add, pow_one] at h₁
  change (shortAngularFrequency T)⁻¹ ^ 2 * ‖(circleH4Jet T t).second‖ ≤ _ at h₂
  change (shortAngularFrequency T)⁻¹ * ‖(circleH4Jet T t).first‖ ≤ _ at h₁
  have h₀ := circle_sine_truncation_l2_error T v hv₀ N
  rw [← hf] at h₀
  change ‖(t : CircleL2 T)‖ ≤ _ at h₀
  constructor
  · rw [short_v_zero_mean T t ht₀]
    exact h₂
  · apply (short_h1_le_derivative_sum T t).trans
    apply (add_le_add h₀ h₁).trans_eq
    have hs₀ := (summable_nat_add_iff N).mpr hv₀
    have hs₁ := (summable_nat_add_iff N).mpr hv₁
    rw [← hs₀.tsum_add hs₁]
    apply tsum_congr
    intro n
    simp only [pow_one, Fin.val_zero, zero_add]
    ring

theorem short_sine_trial_inner {N : ℕ} (v w : Fin N → ℂ) :
    inner ℂ (circleSineTrialH4 T N v : CircleL2 T)
      (circleSineTrialH4 T N w : CircleL2 T) = ∑ j : Fin N, conj (v j) * w j := by
  simp only [circleSineTrialH4, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  change inner ℂ (∑ j : Fin N, v j • circleEvenSineMode T j.val)
    (∑ j : Fin N, w j • circleEvenSineMode T j.val) = _
  have hon := (circle_even_sine_orthonormal T).comp (fun j : Fin N => j.val) Fin.val_injective
  exact hon.inner_sum v w Finset.univ

private theorem short_sine_trial_l2_norm_sq {N : ℕ} (v : Fin N → ℂ) :
    ‖(circleSineTrialH4 T N v : CircleL2 T)‖ ^ 2 = ∑ j : Fin N, ‖v j‖ ^ 2 := by
  calc
    _ = (inner ℂ (circleSineTrialH4 T N v : CircleL2 T)
        (circleSineTrialH4 T N v : CircleL2 T)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (∑ j : Fin N, conj (v j) * v j).re :=
      congrArg Complex.re (short_sine_trial_inner T v v)
    _ = _ := by
      rw [Complex.re_sum]
      apply Finset.sum_congr rfl
      intro j _
      simpa only [RCLike.inner_apply', mul_comm] using!
        (norm_sq_eq_re_inner (𝕜 := ℂ) (v j)).symm

private theorem short_sine_second_mode (j : ℕ) :
    (circleH4Jet T (circleSineH4 T j)).second =
      ((-(shortAngularFrequency T ^ 2 * (2 * (j + 1 : ℕ) : ℝ) ^ 2) : ℝ) : ℂ) •
        (circleSineH4 T j : CircleL2 T) := by
  apply weak_circle_second_unique T (circleSineH4 T j : CircleL2 T) _ _
    (weak_circle_second_of_deriv_chain T _ _ _
      (circleH4Jet T (circleSineH4 T j)).hfirst
      (circleH4Jet T (circleSineH4 T j)).hsecond)
  simpa only [shortAngularFrequency, Nat.cast_add, Nat.cast_one, circleSineH4,
    circleFourierH4, circleEvenSineMode, evenSineMode, Submodule.coe_smul_of_tower,
    Submodule.coe_sub] using!
    circle_sine_mode_weak_second T j

/-- All finite sine normalization tables are actual function-norm identities,
including both weak derivatives.  Complex coefficients are allowed. -/
theorem short_sine_trial_norms_sq {N : ℕ} (v : Fin N → ℂ) :
    ‖(circleSineTrialH4 T N v : CircleL2 T)‖ ^ 2 = (∑ j : Fin N, ‖v j‖ ^ 2) ∧
    shortH1Norm T (circleSineTrialH4 T N v) ^ 2 =
      (∑ j : Fin N, (1 + (2 * (j.val + 1 : ℕ) : ℝ) ^ 2) * ‖v j‖ ^ 2) ∧
    shortVNorm T (circleSineTrialH4 T N v) ^ 2 =
      (∑ j : Fin N, (2 * (j.val + 1 : ℕ) : ℝ) ^ 4 * ‖v j‖ ^ 2) := by
  let f := circleSineTrialH4 T N v
  let lam : Fin N → ℝ := fun j =>
    -(shortAngularFrequency T ^ 2 * (2 * (j.val + 1 : ℕ) : ℝ) ^ 2)
  have hsecond : (circleH4Jet T f).second =
      (circleSineTrialH4 T N (fun j => v j * (lam j : ℂ)) : CircleL2 T) := by
    change circleH4Derivative T 1 (∑ j : Fin N, v j • circleSineH4 T j.val) = _
    simp only [circleSineTrialH4, map_sum, map_smul, Submodule.coe_sum,
      Submodule.coe_smul_of_tower]
    apply Finset.sum_congr rfl
    intro j _
    change v j • (circleH4Jet T (circleSineH4 T j.val)).second =
      (v j * (lam j : ℂ)) • (circleSineH4 T j.val : CircleL2 T)
    rw [short_sine_second_mode, smul_smul]
  have hl2 := short_sine_trial_l2_norm_sq T v
  have hc (j : Fin N) : conj (v j) * v j = ((‖v j‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [RCLike.inner_apply', Complex.ofReal_pow, mul_comm] using!
      inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (v j)
  have hpair (j : Fin N) : conj (v j) * (v j * (lam j : ℂ)) =
      ((lam j * ‖v j‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, hc]
    push_cast
    ring
  have hfirstnorm : ‖(circleH4Jet T f).first‖ ^ 2 = shortAngularFrequency T ^ 2 *
      ∑ j : Fin N, (2 * (j.val + 1 : ℕ) : ℝ) ^ 2 * ‖v j‖ ^ 2 := by
    calc
      _ = (-inner ℂ (f : CircleL2 T) (circleH4Jet T f).second).re := by
        rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
        exact congrArg Complex.re (circle_weak_integration_by_parts T _ _ _ _
          (circleH4Jet T f).hfirst (circleH4Jet T f).hsecond)
      _ = -(∑ j : Fin N, lam j * ‖v j‖ ^ 2) := by
        rw [hsecond]
        change (-inner ℂ (circleSineTrialH4 T N v : CircleL2 T) _).re = _
        rw [short_sine_trial_inner]
        simp only [hpair, Complex.neg_re, Complex.re_sum, Complex.ofReal_re]
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [lam]
        ring
  have hsecondnorm : ‖(circleH4Jet T f).second‖ ^ 2 = shortAngularFrequency T ^ 4 *
      ∑ j : Fin N, (2 * (j.val + 1 : ℕ) : ℝ) ^ 4 * ‖v j‖ ^ 2 := by
    rw [hsecond, short_sine_trial_l2_norm_sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, lam]
    ring
  have hκ := (short_angular_frequency_pos T).ne'
  have hcancel (n : ℕ) : (shortAngularFrequency T)⁻¹ ^ n * shortAngularFrequency T ^ n = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hκ, one_pow]
  refine ⟨hl2, ?_, ?_⟩
  · rw [short_h1_norm_sq, hfirstnorm]
    change ‖(circleSineTrialH4 T N v : CircleL2 T)‖ ^ 2 + _ = _
    rw [hl2, ← mul_assoc, hcancel 2, one_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · rw [short_v_norm_sq, short_sine_trial_mean_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0), zero_add, hsecondnorm,
      ← mul_assoc, hcancel 4, one_mul]

end Lemniscate
