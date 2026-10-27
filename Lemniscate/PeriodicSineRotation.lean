import Lemniscate.PeriodicSineBlockH2

/-! Conditional identification of the L2 constraint vector with the derivative
of a profile square. Reflection symmetry, the positive even Fourier formula,
and vanishing odd modes are explicit hypotheses. They are not inferred from
the even-mode formula alone. The concrete Jacobi identities remain to be proved. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem theta_nome_first_sine_coefficient_pos : 0 < evenCoefficient thetaParameter nome 1 := by
  have hr : 0 < thetaParameter :=
    (by norm_num [rlo] : (0:ℝ) < (rlo:ℝ)).trans_le (actual_nome_theta_r_bounds.mono (J := ⟨rlo,rhi⟩) (by norm_num [rlo, thetaRLower]) (by norm_num [rhi, thetaRUpper])).1
  have hq : 0 < nome := Real.exp_pos _
  have hq1 : nome < 1 := refined_nome_bounds.2.trans_lt (by norm_num [nomeUpper])
  have hd : 0 < 1-nome^2 := sub_pos.mpr (pow_lt_one₀ hq.le hq1 (by decide))
  simpa only [evenCoefficient, Nat.cast_one, mul_one, pow_one] using
    (div_pos (mul_pos (mul_pos (by norm_num : (0:ℝ) < 8) hr) hq) hd)

theorem circle_sine_constraint_coeff_first :
    fourierCoeff (circleSineConstraintVector T) 2 = evenSineFactor := by
  have h := circle_even_sine_mode_coeff_pos T 0 0
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_add, mul_one, ite_true] at h
  simp only [circleSineConstraintVector, circleSineBlockFunction, one_smul,
    circle_fourierCoeff_add, h, circle_sine_tail_coeff_first, add_zero]

theorem circle_sine_constraint_coeff_pos (j : ℕ) (hj : 0 < j) :
    fourierCoeff (circleSineConstraintVector T) (2*(j:ℤ)) =
      (sineRatio thetaParameter nome j:ℂ)*evenSineFactor := by
  by_cases h1 : j = 1
  · subst j
    simp only [Nat.cast_one, mul_one, circle_sine_constraint_coeff_first, sineRatio]
    rw [one_mul, div_self (ne_of_gt theta_nome_first_sine_coefficient_pos)]
    simp
  · have hk : j-2+2 = j := by omega
    conv_lhs => rw [← hk]
    rw [circleSineConstraintVector, circle_sine_block_coeff_pos]
    change (sineRatio thetaParameter nome (j-2+2):ℂ)*evenSineFactor = _
    rw [hk]

theorem circle_sine_constraint_coeff_zero : fourierCoeff (circleSineConstraintVector T) 0 = 0 := by
  simp only [circleSineConstraintVector, circleSineBlockFunction, one_smul,
    circle_fourierCoeff_add, circle_even_sine_mode_coeff_zero, circle_sine_tail_coeff_zero, add_zero]

theorem circle_sine_constraint_coeff_neg (n : ℤ) :
    fourierCoeff (circleSineConstraintVector T) (-n) =
      -fourierCoeff (circleSineConstraintVector T) n := by
  simp only [circleSineConstraintVector, circleSineBlockFunction, one_smul,
    circle_fourierCoeff_add, circle_even_sine_mode_coeff_neg, circle_sine_tail_coeff_neg, neg_add]

theorem circle_sine_constraint_coeff_odd (n : ℤ) :
    fourierCoeff (circleSineConstraintVector T) (2*n+1) = 0 := by
  simp only [circleSineConstraintVector, circleSineBlockFunction, one_smul,
    circle_fourierCoeff_add, circle_even_sine_mode_coeff_odd, circle_sine_tail_coeff_odd, add_zero]

noncomputable def circleSineRotationScale : ℂ :=
  circleFrequencyFactor T 2*(evenCoefficient thetaParameter nome 1:ℂ)/evenSineFactor

theorem circle_sine_rotation_scale_ne_zero : circleSineRotationScale T ≠ 0 := by
  apply div_ne_zero _ evenSineFactor_ne_zero
  apply mul_ne_zero
  · unfold circleFrequencyFactor
    apply mul_ne_zero _ Complex.I_ne_zero
    apply Complex.ofReal_ne_zero.mpr
    have hT : T ≠ 0 := ne_of_gt (Fact.out : 0 < T)
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hT) (by norm_num)
  · exact_mod_cast ne_of_gt theta_nome_first_sine_coefficient_pos

theorem circle_sine_fourier_ext (f g : CircleL2 T)
    (hpos : ∀ j : ℕ, fourierCoeff f (2*(j:ℤ)) = fourierCoeff g (2*(j:ℤ)))
    (hfneg : ∀ n : ℤ, fourierCoeff f (-n) = -fourierCoeff f n)
    (hgneg : ∀ n : ℤ, fourierCoeff g (-n) = -fourierCoeff g n)
    (hfodd : ∀ n : ℤ, fourierCoeff f (2*n+1) = 0)
    (hgodd : ∀ n : ℤ, fourierCoeff g (2*n+1) = 0) : f = g := by
  have hnat (n : ℕ) : fourierCoeff f (n:ℤ) = fourierCoeff g (n:ℤ) := by
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · have he : (n:ℤ) = 2*(j:ℤ) := by exact_mod_cast (by omega : n = 2*j)
      rw [he, hpos]
    · have he : (n:ℤ) = 2*(j:ℤ)+1 := by exact_mod_cast hj
      rw [he, hfodd, hgodd]
  apply circle_fourier_ext T
  intro n
  cases n with
  | ofNat n => exact hnat n
  | negSucc n =>
    change fourierCoeff f (-((n+1:ℕ):ℤ)) = fourierCoeff g (-((n+1:ℕ):ℤ))
    rw [hfneg, hgneg, hnat]

theorem circle_sine_rotation_derivative (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, 0 < j → fourierCoeff h (2*(j:ℤ)) =
      (evenCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff h (2*n+1) = 0) :
    circleContinuousL2 T h₁ = circleSineRotationScale T • circleSineConstraintVector T := by
  apply circle_sine_fourier_ext
  · intro j
    by_cases hj : j = 0
    · subst j
      simp only [Nat.cast_zero, mul_zero, circle_continuous_l2_fourier,
        fourierCoeff_classical_deriv T h h₁ hh, circleFrequencyFactor,
        Int.cast_zero, Complex.ofReal_zero, circle_fourierCoeff_smul,
        circle_sine_constraint_coeff_zero, zero_mul]
    · rw [circle_continuous_l2_fourier, fourierCoeff_classical_deriv T h h₁ hh,
        hc j (Nat.pos_of_ne_zero hj), circle_fourierCoeff_smul,
        circle_sine_constraint_coeff_pos T j (Nat.pos_of_ne_zero hj)]
      unfold circleSineRotationScale sineRatio circleFrequencyFactor
      push_cast
      field_simp [evenSineFactor_ne_zero,
        Complex.ofReal_ne_zero.mpr (ne_of_gt theta_nome_first_sine_coefficient_pos)]
      <;> ring
  · intro n
    simp only [circle_continuous_l2_fourier, fourierCoeff_classical_deriv T h h₁ hh,
      circle_frequency_factor_neg, hs, neg_mul]
  · intro n
    simp only [circle_fourierCoeff_smul, circle_sine_constraint_coeff_neg, mul_neg]
  · intro n
    simp only [circle_continuous_l2_fourier, fourierCoeff_classical_deriv T h h₁ hh, ho, mul_zero]
  · intro n
    simp only [circle_fourierCoeff_smul, circle_sine_constraint_coeff_odd, mul_zero]

theorem circle_sine_rotation_orthogonal_iff (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, 0 < j → fourierCoeff h (2*(j:ℤ)) =
      (evenCoefficient thetaParameter nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff h (2*n+1) = 0) (f : CircleL2 T) :
    inner ℂ (circleContinuousL2 T h₁) f = 0 ↔
      inner ℂ (circleSineConstraintVector T) f = 0 := by
  rw [circle_sine_rotation_derivative T h h₁ hh hs hc ho, inner_smul_left]
  simp only [mul_eq_zero, map_eq_zero, circle_sine_rotation_scale_ne_zero, false_or]

end Lemniscate
