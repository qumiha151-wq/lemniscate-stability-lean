import Lemniscate.ShortInverseSineNorm
import Lemniscate.ShortAdjointFiniteBounds
import Lemniscate.ShortAnchorNorm
import Lemniscate.NeutralHouseholder

/-! The finite weighted norm comparisons are bounds for the actual shifted
rotation vector, with its actual real Householder denominator. -/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private def shiftedSine (i : Fin 7) : ℝ :=
  shortRotationSine shortActualCoefficient i + if i = 0 then 1 else 0

private theorem shifted_rotation_representation :
    circleShortRotationApproximation T + circleHouseholderAnchorH4 T =
      I • circleSineTrialH4 T 7 (fun i => (shiftedSine i : ℂ)) := by
  have hδ : circleSineTrialH4 T 7
      (fun i => ((if i = 0 then 1 else 0 : ℝ) : ℂ)) = circleSineH4 T 0 := by
    simp [circleSineTrialH4, apply_ite]
  rw [circleShortRotationApproximation, short_anchor_eq_I_sine, ← hδ, ← smul_add]
  congr 1
  simp only [circleSineTrialH4, shiftedSine, Complex.ofReal_add, add_smul,
    Finset.sum_add_distrib]

private theorem finite_anchor_pairing :
    inner ℂ (circleHouseholderAnchor T) (circleShortRotationApproximation T : CircleL2 T) =
      (shortRotationSine shortActualCoefficient 0 : ℂ) := by
  have ha : circleHouseholderAnchor T = I • circleEvenSineMode T 0 := by
    simpa only [circle_householder_anchor_h4_coe] using!
      congrArg (fun f : circleH4Domain T => (f : CircleL2 T)) (short_anchor_eq_I_sine T)
  rw [ha, circleShortRotationApproximation]
  simp only [Submodule.coe_smul_of_tower, inner_smul_left, inner_smul_right,
    ← mul_assoc, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  simp only [circleSineTrialH4, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  change inner ℂ (circleEvenSineMode T 0)
    (∑ i : Fin 7, (shortRotationSine shortActualCoefficient i : ℂ) •
      circleEvenSineMode T i.val) = _
  have hon := (circle_even_sine_orthonormal T).comp (fun i : Fin 7 => i.val) Fin.val_injective
  simpa only [Function.comp_def] using!
    hon.inner_right_sum (fun i => (shortRotationSine shortActualCoefficient i : ℂ))
      (Finset.mem_univ (0 : Fin 7))

private theorem inverse_phase_norm (w : ℤ → ℝ) (hw : ∀ n, 1 ≤ w n) (f : CircleL2 T) :
    ‖shortInverseWeightFourier T w hw (I • f)‖ = ‖shortInverseWeightFourier T w hw f‖ := by
  have he := (shortInverseWeightFourierCLM T w hw).map_smul I f
  simp only [short_inverse_fourier_clm_apply, RingHom.id_apply] at he
  rw [he, norm_smul, Complex.norm_I, one_mul]

private theorem reciprocal_v_weight (i : Fin 7) :
    (Lemniscate.shortVWeight (2 * ((i.val + 1 : ℕ) : ℤ)))⁻¹ ^ 2 =
      ((1 / CoarseArithmetic.shortVWeight i : ℚ) : ℝ) := by
  have hn : (2 : ℝ) ≤ 2 * ((i.val + 1 : ℕ) : ℝ) := by norm_num
  have hpow : (1 : ℝ) ≤ (2 * ((i.val + 1 : ℕ) : ℝ)) ^ 4 := by
    nlinarith [sq_nonneg ((2 * ((i.val + 1 : ℕ) : ℝ)) ^ 2 - 2)]
  rw [inv_pow, short_v_weight_sq]
  simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [max_eq_right hpow]
  norm_num [CoarseArithmetic.shortVWeight, div_eq_mul_inv]

private theorem reciprocal_h1_weight (i : Fin 7) :
    (Lemniscate.shortH1Weight (2 * ((i.val + 1 : ℕ) : ℤ)))⁻¹ ^ 2 =
      ((1 / CoarseArithmetic.shortH1Weight i : ℚ) : ℝ) := by
  rw [inv_pow, short_h1_weight_sq]
  norm_num [CoarseArithmetic.shortH1Weight, div_eq_mul_inv]

/-- The four finite weighted comparisons and the denominator are statements
about the actual H4 vector, not just the interval data. -/
theorem short_finite_householder_data :
    let e₇ := circleShortRotationApproximation T
    let a := circleHouseholderAnchorH4 T
    let u := e₇ + a
    ∃ d : ℝ, (1981 / 1000 : ℝ) < d ∧
      1 + inner ℂ (e₇ : CircleL2 T) (a : CircleL2 T) = (d : ℂ) ∧
      shortVNorm T u < 849 / 100 ∧
      ‖shortInverseWeightFourier T Lemniscate.shortVWeight short_v_weight_one_le
        (u : CircleL2 T)‖ < 499 / 1000 ∧
      shortH1Norm T u < 4499 / 1000 ∧
      ‖shortInverseWeightFourier T Lemniscate.shortH1Weight short_h1_weight_one_le
        (u : CircleL2 T)‖ < 889 / 1000 := by
  let x : Fin 7 → ℝ := shiftedSine
  let F := circleSineTrialH4 T 7 (fun i => (x i : ℂ))
  let u := circleShortRotationApproximation T + circleHouseholderAnchorH4 T
  have hshape : u = I • F := shifted_rotation_representation T
  have hx (i : Fin 7) : Contains (shortShiftedRotationInput i) (x i) :=
    short_shifted_rotation_input_sound i
  obtain ⟨_, _, _, _, _, hV, hDV, hH, hDH, hd⟩ := short_seven_norm_certificate
  have hv := short_seven_square_bound shortShiftedRotationInput x CoarseArithmetic.shortVWeight
    ((849 / 100 : ℚ) ^ 2) hx hV
  have hdv := short_seven_square_bound shortShiftedRotationInput x
    (fun i => 1 / CoarseArithmetic.shortVWeight i) ((499 / 1000 : ℚ) ^ 2) hx hDV
  have hh := short_seven_square_bound shortShiftedRotationInput x CoarseArithmetic.shortH1Weight
    ((4499 / 1000 : ℚ) ^ 2) hx hH
  have hdh := short_seven_square_bound shortShiftedRotationInput x
    (fun i => 1 / CoarseArithmetic.shortH1Weight i) ((889 / 1000 : ℚ) ^ 2) hx hDH
  norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] at hdv hdh
  have hVsum := (short_sine_trial_norms_sq T (fun i => (x i : ℂ))).2.2
  have hHsum := (short_sine_trial_norms_sq T (fun i => (x i : ℂ))).2.1
  have hv₂ : shortVNorm T u ^ 2 < (849 / 100 : ℝ) ^ 2 := by
    rw [hshape, short_v_norm_smul, Complex.norm_I, one_mul, hVsum]
    simpa [CoarseArithmetic.shortVWeight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hv
  have hh₂ : shortH1Norm T u ^ 2 < (4499 / 1000 : ℝ) ^ 2 := by
    rw [hshape, short_h1_norm_smul, Complex.norm_I, one_mul, hHsum]
    simpa [CoarseArithmetic.shortH1Weight, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh
  have hsV : ∀ n : ℤ, Lemniscate.shortVWeight (-n) = Lemniscate.shortVWeight n := by
    intro n
    simp [Lemniscate.shortVWeight, Int.cast_neg, neg_sq]
  have hsH : ∀ n : ℤ, Lemniscate.shortH1Weight (-n) = Lemniscate.shortH1Weight n := by
    intro n
    simp [Lemniscate.shortH1Weight, Int.cast_neg, neg_sq]
  have hdv₂ : ‖shortInverseWeightFourier T Lemniscate.shortVWeight short_v_weight_one_le
      (u : CircleL2 T)‖ ^ 2 < (499 / 1000 : ℝ) ^ 2 := by
    rw [hshape]
    change ‖shortInverseWeightFourier T Lemniscate.shortVWeight short_v_weight_one_le
      (I • (F : CircleL2 T))‖ ^ 2 < _
    rw [inverse_phase_norm, short_inverse_sine_norm_sq T _ _ hsV]
    norm_num only [reciprocal_v_weight, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Rat.cast_div, Rat.cast_one] at ⊢
    exact hdv
  have hdh₂ : ‖shortInverseWeightFourier T Lemniscate.shortH1Weight short_h1_weight_one_le
      (u : CircleL2 T)‖ ^ 2 < (889 / 1000 : ℝ) ^ 2 := by
    rw [hshape]
    change ‖shortInverseWeightFourier T Lemniscate.shortH1Weight short_h1_weight_one_le
      (I • (F : CircleL2 T))‖ ^ 2 < _
    rw [inverse_phase_norm, short_inverse_sine_norm_sq T _ _ hsH]
    norm_num only [reciprocal_h1_weight, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Rat.cast_div, Rat.cast_one] at ⊢
    exact hdh
  let d := 1 + shortRotationSine shortActualCoefficient 0
  have hdpos : (1981 / 1000 : ℝ) < d := by
    have hb := (short_shifted_rotation_input_sound (0 : Fin 7)).1
    have hd' : (1981 / 1000 : ℝ) < (shortShiftedRotationInput 0).lo := by
      have hnum : ((1981 / 1000 : ℚ) : ℝ) = (1981 / 1000 : ℝ) := by norm_num
      have hc : (((1981 / 1000 : ℚ) : ℝ)) < ((shortShiftedRotationInput 0).lo : ℝ) :=
        Rat.cast_lt.mpr hd
      simpa only [hnum] using! hc
    dsimp only [d]
    simpa only [if_pos rfl, ite_true, add_comm] using! hd'.trans_le hb
  have hden : 1 + inner ℂ (circleShortRotationApproximation T : CircleL2 T)
      (circleHouseholderAnchorH4 T : CircleL2 T) = (d : ℂ) := by
    have hp := finite_anchor_pairing T
    have hp' : inner ℂ (circleShortRotationApproximation T : CircleL2 T)
        (circleHouseholderAnchor T) = (shortRotationSine shortActualCoefficient 0 : ℂ) := by
      rw [← inner_conj_symm, hp, Complex.conj_ofReal]
    simpa only [circle_householder_anchor_h4_coe, hp', d, Complex.ofReal_add,
      Complex.ofReal_one]
  refine ⟨d, hdpos, hden, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hv₂, short_v_norm_nonneg T u]
  · nlinarith only [hdv₂, norm_nonneg
      (shortInverseWeightFourier T Lemniscate.shortVWeight short_v_weight_one_le (u : CircleL2 T))]
  · nlinarith only [hh₂, short_h1_norm_nonneg T u]
  · nlinarith only [hdh₂, norm_nonneg
      (shortInverseWeightFourier T Lemniscate.shortH1Weight short_h1_weight_one_le (u : CircleL2 T))]

/-- The finite Householder map has the exact L2 isometry and Green symmetry
used in the actual form comparison. -/
theorem short_finite_householder_symmetries :
    let e := (circleShortRotationApproximation T : CircleL2 T)
    let a := circleHouseholderAnchor T
    inner ℂ a e = inner ℂ e a ∧
    (∀ f : CircleL2 T, ‖neutralHouseholder e a f‖ = ‖f‖) ∧
      ∀ f g : CircleL2 T, inner ℂ (neutralHouseholder e a f) g =
        inner ℂ f (neutralHouseholder e a g) := by
  let e := (circleShortRotationApproximation T : CircleL2 T)
  let a := circleHouseholderAnchor T
  obtain ⟨d, hd, hden, _, _, _, _⟩ := short_finite_householder_data T
  have he : inner ℂ e e = 1 := by
    rw [inner_self_eq_norm_sq_to_K, (short_actual_finite_vector_bounds T).1]
    norm_num
  have hea : inner ℂ a e = inner ℂ e a := by
    rw [finite_anchor_pairing T]
    rw [← inner_conj_symm, finite_anchor_pairing T, Complex.conj_ofReal]
  have hden' : 1 + inner ℂ e a = (d : ℂ) := by
    simpa only [e, a, circle_householder_anchor_h4_coe] using! hden
  have hdne : 1 + inner ℂ e a ≠ 0 := by
    rw [hden']
    exact_mod_cast ne_of_gt (lt_trans (by norm_num : (0 : ℝ) < 1981 / 1000) hd)
  exact ⟨hea, fun f => neutral_householder_norm e a he (circle_householder_anchor_unit T) hea hdne f,
    fun f g => neutral_householder_selfadjoint e a hea f g⟩

end Lemniscate
