import Lemniscate.PeriodicLowHighEntry
import Lemniscate.CoefficientMajorant
import Lemniscate.PeriodicSineAdjointTrial
import Lemniscate.EvenCouplingArithmetic

/-! Analytic high-frequency estimates for low sine polynomials. The profile
Fourier identities remain explicit until the concrete profile is identified. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_even_coefficient_distance_bound (h : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (k j : ℤ) (a : ℕ) (hk : a < k.natAbs) (hj : j.natAbs ≤ a) :
    ‖fourierCoeff h (2*(k-j))‖ ≤
      6*((k.natAbs-a:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-a) := by
  have htriangle : k.natAbs ≤ (k-j).natAbs+j.natAbs := by
    simpa only [sub_add_cancel] using Int.natAbs_add_le (k-j) j
  have hdiff : k.natAbs-a ≤ (k-j).natAbs := by omega
  have hpos : 0 < k.natAbs-a := by omega
  rw [circle_even_integer_coefficient T h thetaParameter nome hs hc,
    Complex.norm_real,Real.norm_eq_abs]
  have hH : (H:ℝ) ≤ 6 := by norm_num [H,rhi,qb]
  calc
    _ ≤ (H:ℝ)*(((k.natAbs-a:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-a)) :=
      common_index_coefficient_majorant _ _ hpos hdiff
    _ ≤ _ := by
      have hq : 0 ≤ (qb:ℝ) := by norm_num [qb]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hH)
        (mul_nonneg (Nat.cast_nonneg (k.natAbs-a)) (pow_nonneg hq (k.natAbs-a)))]

private theorem sine_factor_norm_le_one : ‖evenSineFactor‖ ≤ 1 := by
  have h := congrArg norm evenSineFactor_normalization
  simp only [norm_mul,Complex.norm_conj,norm_one] at h
  norm_num at h
  nlinarith only [h,norm_nonneg evenSineFactor]

theorem circle_low_sine_action_high_bound (A : circleH4Domain T →ₗ[ℂ] CircleL2 T)
    (n : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ m : ℤ, m.natAbs ≤ 10 →
      ‖fourierCoeff (A (circleFourierH4 T (2*m))) n‖ ≤ 30*(n:ℝ)^2*C)
    (v : Fin 10 → ℂ) (hv : ∑ j, ‖v j‖ ≤ 5) :
    ‖fourierCoeff (A (circleSineTrialH4 T 10 v)) n‖ ≤ 300*(n:ℝ)^2*C := by
  have hf (f : CircleL2 T) : fourierCoeff f n = inner ℂ (fourierBasis (T := T) n) f := by
    rw [← HilbertBasis.repr_apply_apply,fourierBasis_repr]
  have hm (j : Fin 10) : ((j.val+1:ℕ):ℤ).natAbs ≤ 10 := by simp only [Int.natAbs_natCast]; omega
  have hb' (m : ℤ) (hm : m.natAbs ≤ 10) :
      ‖inner ℂ (fourierBasis (T := T) n) (A (circleFourierH4 T (2*m)))‖ ≤
        30*(n:ℝ)^2*C := by simpa only [hf] using hb m hm
  rw [hf]
  simp only [circleSineTrialH4,circleSineH4,map_sum,map_smul,map_sub,
    inner_sum,inner_smul_right,inner_sub_right]
  calc
    _ ≤ ∑ j : Fin 10, ‖v j‖*(60*(n:ℝ)^2*C) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,norm_mul]
      calc
        _ ≤ ‖v j‖*(1*(30*(n:ℝ)^2*C+30*(n:ℝ)^2*C)) := by
          gcongr
          · exact sine_factor_norm_le_one
          · apply (norm_sub_le _ _).trans
            refine add_le_add (hb' _ (hm j)) ?_
            simpa only [mul_neg] using hb' (-((j.val+1:ℕ):ℤ))
              (by simpa only [Int.natAbs_neg] using hm j)
        _ = _ := by ring
    _ = (∑ j : Fin 10, ‖v j‖)*(60*(n:ℝ)^2*C) := by rw [Finset.sum_mul]
    _ ≤ 5*(60*(n:ℝ)^2*C) := mul_le_mul_of_nonneg_right hv (by positivity)
    _ = _ := by ring

theorem circle_bloch_low_sine_high_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) (j : Fin 5) (k : ℤ) (hk : 16 ≤ k.natAbs)
    (v : Fin 10 → ℂ) (hv : ∑ i, ‖v i‖ ≤ 5) :
    ‖fourierCoeff (circleBlochCoefficient T h h₁ h₂ j (circleSineTrialH4 T 10 v)) (2*k)‖ ≤
      1800*(2*(k:ℝ))^2*((k.natAbs-10:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-10) ∧
    ‖fourierCoeff (circleBlochAdjointCoefficient T h h₁ h₂ j (circleSineTrialH4 T 10 v)) (2*k)‖ ≤
      1800*(2*(k:ℝ))^2*((k.natAbs-10:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-10) := by
  let C : ℝ := 6*((k.natAbs-10:ℕ):ℝ)*(qb:ℝ)^(k.natAbs-10)
  have hC : 0 ≤ C := by dsimp only [C]; norm_num [qb] <;> positivity
  have hhigh : 32 ≤ |((2*k:ℤ):ℝ)| := by
    have h : (16:ℝ) ≤ |(k:ℝ)| := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (16:ℝ) ≤ (k.natAbs:ℝ) by exact_mod_cast hk)
    simpa only [Int.cast_mul,Int.cast_ofNat,abs_mul,show |(2:ℝ)| = 2 by norm_num] using
      (show (32:ℝ) ≤ 2*|(k:ℝ)| by linarith only [h])
  have hlow (m : ℤ) (hm : m.natAbs ≤ 10) : |((2*m:ℤ):ℝ)| ≤ 20 := by
    have h : |(m:ℝ)| ≤ 10 := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (m.natAbs:ℝ) ≤ 10 by exact_mod_cast hm)
    simpa only [Int.cast_mul,Int.cast_ofNat,abs_mul,show |(2:ℝ)| = 2 by norm_num] using
      (show (2:ℝ)*|(m:ℝ)| ≤ 20 by linarith only [h])
  have hb (m : ℤ) (hm : m.natAbs ≤ 10) :
      ‖fourierCoeff (circleBlochCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*k)‖ ≤
        30*((2*k:ℤ):ℝ)^2*C ∧
      ‖fourierCoeff (circleBlochAdjointCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*k)‖ ≤
        30*((2*k:ℤ):ℝ)^2*C := by
    have he := circle_bloch_low_high_entry_bound T h hr j (2*k) (2*m) hhigh (hlow m hm)
    have hp : ‖fourierCoeff h (2*k-2*m)‖ ≤ C := by
      simpa only [mul_sub,C] using circle_even_coefficient_distance_bound T h hs hc k m 10 (by omega) hm
    have hp' : ‖fourierCoeff h (2*m-2*k)‖ ≤ C := by
      have heq : 2*m-2*k = -(2*k-2*m) := by ring
      rw [heq,hs]
      exact hp
    constructor
    · rw [circle_bloch_coefficient_basis_fourier T h h₁ h₂ hh hh₁]
      exact he.1.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    · rw [circle_bloch_adjoint_basis_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real,Complex.norm_conj]
      exact he.2.trans (mul_le_mul_of_nonneg_left hp' (by positivity))
  constructor
  · have hbound := circle_low_sine_action_high_bound T (circleBlochCoefficient T h h₁ h₂ j)
      (2*k) C hC (fun m hm => (hb m hm).1) v hv
    convert hbound using 1 <;> simp only [C,Int.cast_mul,Int.cast_ofNat] <;> ring
  · have hbound := circle_low_sine_action_high_bound T (circleBlochAdjointCoefficient T h h₁ h₂ j)
      (2*k) C hC (fun m hm => (hb m hm).2) v hv
    convert hbound using 1 <;> simp only [C,Int.cast_mul,Int.cast_ofNat] <;> ring

end Lemniscate
