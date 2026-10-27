import Lemniscate.PeriodicFixedTrialResidual
import Lemniscate.PeriodicRotationNorm
import Lemniscate.AdjointTrialPairing
import Lemniscate.PeriodicAdjointNeutral

/-! Identification of the rational trial pairing with the actual unit
rotation vector. The positive sine convention is the negative of q q'. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

section Profile
variable (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter)

include hq hp he hqreal hpreal hc hr in
theorem circle_rotation_coefficient_norm_relation :
    rotationCoefficientNorm*(2*Real.pi/T) =
      Real.sqrt 2*‖circleContinuousL2 T (q*p)‖ := by
  have hn := rotation_coefficient_norm_bounds.1
  have hκ : 0 < 2*Real.pi/T := div_pos (by positivity) (Fact.out : 0 < T)
  have hm := circle_rotation_norm_sq T q p hq hp he hqreal hpreal
  have hc0 := hc 0
  norm_num only [Nat.cast_zero,mul_zero,fourierCoefficient,if_pos rfl,ite_true] at hc0
  rw [hc0,Complex.ofReal_re] at hm
  have hh0 : 0 ≤ constantCoefficient thetaParameter nome := by
    nlinarith only [sq_nonneg ‖circleContinuousL2 T (q*p)‖,hm]
  have hr0 : 0 < thetaParameter := by rw [← hr]; positivity
  have harg : 0 ≤ 2*constantCoefficient thetaParameter nome/(5*thetaParameter) :=
    div_nonneg (mul_nonneg (by norm_num) hh0) (by positivity)
  have hsq : rotationCoefficientNorm^2*(2*Real.pi/T)^2 =
      2*‖circleContinuousL2 T (q*p)‖^2 := by
    rw [rotationCoefficientNorm,Real.sq_sqrt harg,hr]
    rw [hm]
    field_simp [ne_of_gt hr0]
    <;> ring
  apply (sq_eq_sq₀ (mul_nonneg hn.le hκ.le)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  exact hsq

include hq hp he hqreal hpreal hs hc hr in
theorem circle_sine_mode_positive_rotation_pairing (j : ℕ) :
    inner ℂ (circleEvenSineMode T j) (-circleUnitRotation T q p) =
      ((2*((j+1:ℕ):ℝ)*evenCoefficient thetaParameter nome (j+1)/
        rotationCoefficientNorm:ℝ):ℂ) := by
  let N := ‖circleContinuousL2 T (q*p)‖
  have hn := rotation_coefficient_norm_bounds.1
  have hκ : 0 < 2*Real.pi/T := div_pos (by positivity) (Fact.out : 0 < T)
  have hscale := circle_rotation_coefficient_norm_relation T q p hq hp he hqreal hpreal hc hr
  have hN : 0 < N := by
    have hprod : 0 < Real.sqrt 2*N := by
      change 0 < Real.sqrt 2*‖circleContinuousL2 T (q*p)‖
      rw [← hscale]
      exact mul_pos hn hκ
    exact ((mul_pos_iff.mp hprod).resolve_right (by
      intro h
      exact (not_lt_of_ge (Real.sqrt_nonneg _)) h.1)).2
  have hsqrt : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hratio : (2*Real.pi/T)/(Real.sqrt 2*N) = 1/rotationCoefficientNorm := by
    apply (div_eq_div_iff (mul_ne_zero hsqrt hN.ne') hn.ne').mpr
    simpa only [one_mul,mul_comm] using hscale
  have hd (n : ℤ) : fourierCoeff (circleContinuousL2 T (q*p)) n =
      circleFrequencyFactor T n*fourierCoeff (q^2 : C(AddCircle T, ℂ)) n/2 := by
    have h := fourierCoeff_classical_deriv T _ _ (circle_profile_square_deriv T q p hq) n
    rw [circle_continuous_fourier_smul] at h
    rw [circle_continuous_l2_fourier]
    linear_combination (1/2:ℂ)*h
  calc
    _ = (((2*Real.pi/T)/(Real.sqrt 2*N):ℝ):ℂ)*
        ((2*((j+1:ℕ):ℝ)*evenCoefficient thetaParameter nome (j+1):ℝ):ℂ) := by
      change inner ℂ (evenSineFactor •
        (fourierBasis (T := T) (2*((j+1:ℕ):ℤ))-
         fourierBasis (T := T) (-(2*((j+1:ℕ):ℤ)))))
          (-((N:ℂ)⁻¹ • circleContinuousL2 T (q*p))) = _
      rw [inner_neg_right,inner_smul_right,inner_smul_left,inner_sub_left]
      simp only [← HilbertBasis.repr_apply_apply,fourierBasis_repr,hd,
        circle_frequency_factor_neg,hs,hc,fourierCoefficient,
        if_neg (by omega : j+1 ≠ 0)]
      simp only [evenSineFactor,evenCosineFactor,circleFrequencyFactor,
        map_mul,map_neg,Complex.conj_I,Complex.conj_ofReal]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr hsqrt,Complex.ofReal_ne_zero.mpr hN.ne']
      <;> simp only [Complex.I_sq]
      <;> ring
    _ = _ := by rw [hratio]; push_cast; ring

include hq hp he hqreal hpreal hs hc hr in
theorem circle_adjoint_trial_rotation_pairing :
    inner ℂ (circleAdjointTrial T : CircleL2 T) (-circleUnitRotation T q p) =
      (adjointTrialPairing:ℂ) := by
  change inner ℂ (∑ j : Fin 18, (adjointTrialCoefficient j:ℂ) • circleEvenSineMode T j.val)
    (-circleUnitRotation T q p) = _
  simp only [sum_inner,inner_smul_left,map_ratCast,
    circle_sine_mode_positive_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr]
  simp only [adjointTrialPairing,Complex.ofReal_div,Complex.ofReal_sum,
    Complex.ofReal_mul,Complex.ofReal_ratCast,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

include hq hp he hqreal hpreal hs hc hr in
theorem circle_normalized_adjoint_trial_residual_sq
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (σ : ℂ) (hσ : ‖σ‖ = 1) :
    ‖circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p))
      (circleNormalizedTrial T (σ • circleUnitRotation T q p) (circleAdjointTrial T))‖^2 <
        (2:ℝ)/10^30 := by
  have hpair := circle_adjoint_trial_rotation_pairing T q p hq hp he hqreal hpreal hs hc hr
  rw [inner_neg_right] at hpair
  have hpair' : inner ℂ (circleAdjointTrial T : CircleL2 T) (circleUnitRotation T q p) =
      -(adjointTrialPairing:ℂ) := by linear_combination -hpair
  have hpairnorm : 1 < ‖inner ℂ (circleAdjointTrial T : CircleL2 T)
      (σ • circleUnitRotation T q p)‖ := by
    rw [inner_smul_right,norm_mul,hσ,one_mul,hpair',norm_neg,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (lt_trans (by norm_num : (0:ℝ) < 1) adjoint_trial_pairing_gt_one)]
    exact adjoint_trial_pairing_gt_one
  have hraw := circle_adjoint_trial_residual_sq T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he)
    (by intro x; change conj ((q x)^2) = (q x)^2; simp only [map_pow,hqreal])
    (by intro x; change conj (2*(q x*p x)) = 2*(q x*p x)
        simp only [map_mul,map_ofNat,hqreal,hpreal])
    (by intro x; change conj (1-3*(q x)^4) = 1-3*(q x)^4
        simp only [map_sub,map_one,map_mul,map_ofNat,map_pow,hqreal])
    hs ho hc hr
  rw [circle_normalized_trial_adjoint_norm]
  exact (pow_le_pow_left₀ (by positivity)
    (div_le_self (norm_nonneg _) hpairnorm.le) 2).trans_lt hraw

end Profile
end Lemniscate
