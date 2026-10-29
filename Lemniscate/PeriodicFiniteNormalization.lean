import Lemniscate.PeriodicApproximationBounds

/-! Exact normalization and L2 distance of the two finite approximations.
These are identities and bounds for periodic functions, not only sequences. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_real_sine_trial_inner {N : ℕ} (v w : Fin N → ℝ) :
    inner ℂ (circleSineTrialH4 T N (fun j => (v j:ℂ)) : CircleL2 T)
      (circleSineTrialH4 T N (fun j => (w j:ℂ)) : CircleL2 T) =
        ((∑ j : Fin N, v j*w j:ℝ):ℂ) := by
  simp only [circleSineTrialH4,Submodule.coe_sum,Submodule.coe_smul_of_tower]
  change inner ℂ (∑ j : Fin N, (v j:ℂ) • circleEvenSineMode T j.val)
    (∑ j : Fin N, (w j:ℂ) • circleEvenSineMode T j.val) = _
  have hon := (circle_even_sine_orthonormal T).comp (fun j : Fin N => j.val) Fin.val_injective
  simpa only [Function.comp_def,Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul] using
    hon.inner_sum (fun j => (v j:ℂ)) (fun j => (w j:ℂ)) Finset.univ

private theorem real_sine_norm_sq {N : ℕ} (v : Fin N → ℝ) :
    ‖(circleSineTrialH4 T N (fun j => (v j:ℂ)) : CircleL2 T)‖^2 =
      ∑ j : Fin N, (v j)^2 := by
  have h := congrArg Complex.re (circle_real_sine_trial_inner T v v)
  simpa [inner_self_eq_norm_sq_to_K,pow_two] using h

private theorem finite_difference_square_sum :
    (∑ j : Fin 15, (finiteDifferenceCoefficient j)^2) < (1:ℝ)/400 := by
  have hb : (∑ j : Fin 15, (finiteDifferenceCoefficient j)^2) ≤
      ((∑ j : Fin 15, (absUpper (differenceFiniteData j))^2:ℚ):ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (abs_nonneg (finiteDifferenceCoefficient j))
      (absUpper_sound _ _ (difference_finite_data_sound j)) 2
    simpa only [sq_abs] using h
  have hn : ((∑ j : Fin 15, (absUpper (differenceFiniteData j))^2:ℚ):ℝ) < (1:ℝ)/400 := by
    have hx : ((∑ j : Fin 15, (absUpper (differenceFiniteData j))^2:ℚ):ℝ) < ((1/400:ℚ):ℝ) :=
      Rat.cast_lt.mpr vector_error_comparisons.2.2.2.2.1
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hx
  exact hb.trans_lt hn

theorem circle_finite_normalization_bounds :
    ‖(circleRotationApproximation T : CircleL2 T)‖ = 1 ∧
    inner ℂ (circleAdjointApproximation T : CircleL2 T)
      (circleRotationApproximation T : CircleL2 T) = 1 ∧
    ‖((circleAdjointApproximation T-circleRotationApproximation T : circleH4Domain T) : CircleL2 T)‖ <
      (1:ℝ)/20 := by
  have hte0 : 0 < (rotationFiniteNormData.lo:ℝ) := by
    exact_mod_cast ((by norm_num : (0:ℚ) < 999/1000).trans
      vector_interval_certificate.finite_norm_pos)
  have hte : 0 < rotationFiniteNorm := hte0.trans_le rotation_finite_norm_data_sound.1
  have htp0 : 0 < (adjointFinitePairingData.lo:ℝ) := by
    exact_mod_cast ((by norm_num : (0:ℚ) < 999/1000).trans
      vector_interval_certificate.finite_pair_pos)
  have htp : 0 < adjointFinitePairing := htp0.trans_le adjoint_finite_pairing_data_sound.1
  have hsq : rotationFiniteNorm^2 = ∑ j : Fin 15, (rotationSineCoefficient j.val)^2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have he : (∑ j : Fin 15, (rotationFiniteCoefficient j)^2) = 1 := by
    simp only [rotationFiniteCoefficient,div_pow,← Finset.sum_div,← hsq]
    exact div_self (pow_ne_zero 2 (ne_of_gt hte))
  have hp : (∑ j : Fin 15, adjointFiniteCoefficient j*rotationFiniteCoefficient j) = 1 := by
    simp only [adjointFiniteCoefficient,div_mul_eq_mul_div,← Finset.sum_div]
    change adjointFinitePairing/adjointFinitePairing = 1
    exact div_self (ne_of_gt htp)
  have hdiff : circleAdjointApproximation T-circleRotationApproximation T =
      circleSineTrialH4 T 15 (fun j => (finiteDifferenceCoefficient j:ℂ)) := by
    simp only [circleAdjointApproximation,circleRotationApproximation,circleSineTrialH4,
      finiteDifferenceCoefficient,Complex.ofReal_sub,sub_smul,Finset.sum_sub_distrib]
  refine ⟨?_,?_,?_⟩
  · have hn := real_sine_norm_sq T rotationFiniteCoefficient
    rw [he] at hn
    change ‖(circleRotationApproximation T : CircleL2 T)‖^2 = 1 at hn
    nlinarith only [hn,norm_nonneg (circleRotationApproximation T : CircleL2 T)]
  · change inner ℂ (circleSineTrialH4 T 15 (fun j => (adjointFiniteCoefficient j:ℂ)) : CircleL2 T)
      (circleSineTrialH4 T 15 (fun j => (rotationFiniteCoefficient j:ℂ)) : CircleL2 T) = 1
    rw [circle_real_sine_trial_inner,hp,Complex.ofReal_one]
  · rw [hdiff]
    have hn := real_sine_norm_sq T finiteDifferenceCoefficient
    have hb := finite_difference_square_sum
    nlinarith only [hn,hb]

end Lemniscate
