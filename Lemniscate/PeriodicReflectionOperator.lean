import Lemniscate.PeriodicReflection

/-! Reflection commutes with the actual H4 operator when its zeroth and second
order coefficients are even and its first order coefficient is odd. The
multiplication identity is extended from every Fourier mode to all of L2. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_reflect_basis (m : ℤ) :
    circleReflect T (fourierBasis (T := T) m) = fourierBasis (T := T) (-m) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_reflect_fourier, ← circle_continuous_l2_fourier_basis,
    ← circle_continuous_l2_fourier_basis, circle_continuous_l2_fourier,
    circle_continuous_l2_fourier, circle_continuous_fourier_mode,
    circle_continuous_fourier_mode]
  simp only [neg_eq_iff_eq_neg]

theorem circle_multiply_basis_fourier (h : C(AddCircle T, ℂ)) (m n : ℤ) :
    fourierCoeff (circleMultiplyL2 T h (fourierBasis (T := T) m)) n =
      fourierCoeff h (n-m) := by
  rw [← circle_continuous_l2_fourier_basis, circle_multiply_l2_continuous,
    circle_continuous_l2_fourier, circle_fourier_product_mode]

theorem circle_reflect_multiply_basis (h : C(AddCircle T, ℂ)) (ε : ℂ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = ε*fourierCoeff h n) (m : ℤ) :
    circleReflect T (circleMultiplyL2 T h (fourierBasis (T := T) m)) =
      ε • circleMultiplyL2 T h (circleReflect T (fourierBasis (T := T) m)) := by
  apply circle_fourier_ext T
  intro n
  rw [circle_reflect_fourier, circle_multiply_basis_fourier, circle_fourierCoeff_smul,
    circle_reflect_basis, circle_multiply_basis_fourier]
  rw [show -n-m = -(n+m) by omega, hs, show n-(-m) = n+m by omega]

theorem circle_reflect_multiply (h : C(AddCircle T, ℂ)) (ε : ℂ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = ε*fourierCoeff h n) (f : CircleL2 T) :
    circleReflect T (circleMultiplyL2 T h f) =
      ε • circleMultiplyL2 T h (circleReflect T f) := by
  let R := (circleReflectIsometry T).toContinuousLinearMap
  let F := R.comp (circleMultiplyL2 T h)
  let G := ε • (circleMultiplyL2 T h).comp R
  have hb (m : ℤ) : F (fourierBasis (T := T) m) = G (fourierBasis (T := T) m) :=
    circle_reflect_multiply_basis T h ε hs m
  have hF := ((fourierBasis (T := T)).hasSum_repr f).mapL F
  have hG := ((fourierBasis (T := T)).hasSum_repr f).mapL G
  simp only [map_smul, hb] at hF
  simp only [map_smul] at hG
  exact hF.unique hG

theorem circle_reflect_sub (f g : CircleL2 T) :
    circleReflect T (f-g) = circleReflect T f - circleReflect T g :=
  (circleReflectIsometry T).map_sub f g

theorem circle_h4_operator_reflect (h h₁ h₂ : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hs₁ : ∀ n : ℤ, fourierCoeff h₁ (-n) = -fourierCoeff h₁ n)
    (hs₂ : ∀ n : ℤ, fourierCoeff h₂ (-n) = fourierCoeff h₂ n)
    (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ (circleReflectH4 T f) =
      circleReflect T (circleH4Operator T h h₁ h₂ f) := by
  have h0 (g : CircleL2 T) := circle_reflect_multiply T h 1
    (by simpa only [one_mul] using hs) g
  have h1 (g : CircleL2 T) := circle_reflect_multiply T h₁ (-1)
    (by simpa only [neg_one_mul] using hs₁) g
  have h2 (g : CircleL2 T) := circle_reflect_multiply T h₂ 1
    (by simpa only [one_mul] using hs₂) g
  simp only [one_smul] at h0 h2
  simp only [circle_h4_operator_apply, circleLinearL2Expression,
    circleSymmetricL2Expression, circle_reflect_add, circle_reflect_sub,
    circle_reflect_smul, circle_reflect_h4_first, circle_reflect_h4_second,
    circle_reflect_h4_fourth, h0, h1, h2, map_smul]
  rfl

theorem circle_deriv_reflection_parity (h h₁ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (ε : ℂ)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = ε*fourierCoeff h n) (n : ℤ) :
    fourierCoeff h₁ (-n) = (-ε)*fourierCoeff h₁ n := by
  rw [fourierCoeff_classical_deriv T h h₁ hh, circle_frequency_factor_neg,
    hs, fourierCoeff_classical_deriv T h h₁ hh]
  ring

theorem circle_h4_operator_reflect_of_even (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (f : circleH4Domain T) :
    circleH4Operator T h h₁ h₂ (circleReflectH4 T f) =
      circleReflect T (circleH4Operator T h h₁ h₂ f) := by
  have hs₁ : ∀ n : ℤ, fourierCoeff h₁ (-n) = -fourierCoeff h₁ n := by
    intro n
    simpa only [neg_one_mul] using circle_deriv_reflection_parity T h h₁ hh 1
      (by simpa only [one_mul] using hs) n
  have hs₂ : ∀ n : ℤ, fourierCoeff h₂ (-n) = fourierCoeff h₂ n := by
    intro n
    simpa only [neg_neg, one_mul] using circle_deriv_reflection_parity T h₁ h₂ hh₁ (-1)
      (by simpa only [neg_one_mul] using hs₁) n
  exact circle_h4_operator_reflect T h h₁ h₂ hs hs₁ hs₂ f

end Lemniscate
