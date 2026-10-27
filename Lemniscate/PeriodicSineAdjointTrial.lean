import Lemniscate.PeriodicAdjointTrial
import Lemniscate.PeriodicSineParseval

/-! The adjoint residual in the normalized sine basis. The input index is
the row index of the original operator; the output index is its column index. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSineH4 (j : ℕ) : circleH4Domain T :=
  evenSineFactor • (circleFourierH4 T (2*((j+1:ℕ):ℤ))-
    circleFourierH4 T (-(2*((j+1:ℕ):ℤ))))

noncomputable def circleSineTrialH4 (N : ℕ) (v : Fin N → ℂ) : circleH4Domain T :=
  ∑ j : Fin N, v j • circleSineH4 T j.val

theorem circle_adjoint_sine_trial_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (N : ℕ) (v : Fin N → ℂ) (n : ℤ) :
    fourierCoeff (circleH4FormalAdjoint T h h₁ (circleSineTrialH4 T N v)) n =
      evenSineFactor * ∑ j : Fin N, v j *
        (conj (circleBlochFourierEntry T h 0 (2*((j.val+1:ℕ):ℤ)) n)-
         conj (circleBlochFourierEntry T h 0 (-(2*((j.val+1:ℕ):ℤ))) n)) := by
  have hb (m : ℤ) : inner ℂ (fourierBasis (T := T) n)
      (circleH4FormalAdjoint T h h₁ (circleFourierH4 T m)) =
        conj (circleBlochFourierEntry T h 0 m n) := by
    have hf := circle_adjoint_polynomial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real
      {m} (fun _ => 1) n
    simpa only [Finset.sum_singleton,one_smul,one_mul,← fourierBasis_repr,
      HilbertBasis.repr_apply_apply] using hf
  rw [← fourierBasis_repr,HilbertBasis.repr_apply_apply]
  simp only [circleSineTrialH4,circleSineH4,map_sum,map_smul,map_sub,
    inner_sum,inner_smul_right,inner_sub_right,hb,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem circle_bloch_zero_entry_reflect (h : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (n m : ℤ) :
    circleBlochFourierEntry T h 0 (-n) (-m) = circleBlochFourierEntry T h 0 n m := by
  unfold circleBlochFourierEntry
  rw [show -n-(-m) = -(n-m) by ring,hs]
  simp only [add_zero,neg_inj,Int.cast_neg]
  push_cast
  ring

theorem circle_bloch_zero_entry_odd_column (h : C(AddCircle T, ℂ))
    (ho : ∀ n : ℤ, fourierCoeff h (2*n+1) = 0) (i j : ℤ) :
    circleBlochFourierEntry T h 0 (2*i) (2*j+1) = 0 := by
  have hn : 2*i ≠ 2*j+1 := by omega
  unfold circleBlochFourierEntry
  rw [if_neg hn,show 2*i-(2*j+1) = 2*(i-j-1)+1 by ring,ho]
  simp only [mul_zero,add_zero]

theorem circle_adjoint_sine_trial_sector (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (ho : ∀ n : ℤ, fourierCoeff h (2*n+1) = 0) (N : ℕ) (v : Fin N → ℂ) :
    InCircleEvenSineSector T
      (circleH4FormalAdjoint T h h₁ (circleSineTrialH4 T N v)) := by
  have he (m n : ℤ) : circleBlochFourierEntry T h 0 m (-n) =
      circleBlochFourierEntry T h 0 (-m) n := by
    simpa only [neg_neg] using circle_bloch_zero_entry_reflect T h hs (-m) n
  constructor
  · intro n
    rw [circle_adjoint_sine_trial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
      circle_adjoint_sine_trial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
    simp only [he,neg_neg]
    rw [← mul_neg,← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro n
    rw [circle_adjoint_sine_trial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
    have he' (m : ℤ) : circleBlochFourierEntry T h 0 (-(2*m)) (2*n+1) = 0 := by
      rw [show -(2*m) = 2*(-m) by ring]
      exact circle_bloch_zero_entry_odd_column T h ho (-m) n
    simp only [circle_bloch_zero_entry_odd_column T h ho,he',map_zero,
      sub_self,mul_zero,Finset.sum_const_zero]

theorem circle_adjoint_sine_trial_norm_sq (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (ho : ∀ n : ℤ, fourierCoeff h (2*n+1) = 0) (N : ℕ) (v : Fin N → ℂ) :
    ‖circleH4FormalAdjoint T h h₁ (circleSineTrialH4 T N v)‖^2 =
      ∑' k : ℕ, ‖∑ j : Fin N, v j *
        (conj (circleBlochFourierEntry T h 0 (2*((j.val+1:ℕ):ℤ)) (2*((k+1:ℕ):ℤ)))-
         conj (circleBlochFourierEntry T h 0 (-(2*((j.val+1:ℕ):ℤ))) (2*((k+1:ℕ):ℤ))))‖^2 := by
  rw [circle_even_sine_parseval T _
    (circle_adjoint_sine_trial_sector T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs ho N v)]
  simp only [circle_adjoint_sine_trial_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real,
    norm_mul,mul_pow,tsum_mul_left]
  have hn := congrArg norm evenSineFactor_normalization
  simp only [norm_mul,norm_conj,norm_one] at hn
  norm_num at hn
  have hn2 : 2*‖evenSineFactor‖^2 = 1 := by nlinarith only [hn]
  rw [← mul_assoc,hn2,one_mul]

end Lemniscate
