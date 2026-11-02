import Lemniscate.PeriodicLowHighEntry

/-! The three symmetric Bloch coefficients used in the untransformed
low-high coupling. Their off-diagonal entries are actual Fourier coefficients. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

noncomputable def evenSymmetricOffScalar (r : ℝ) (j : Fin 3) (n m : ℝ) : ℝ :=
  ![r*(45*n*m-(15/4)*(n-m)^2),45*r*(n+m),45*r] j

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleBlochSymmetricCoefficient (h h₁ h₂ : C(AddCircle T, ℂ))
    (j : Fin 3) : circleH4Domain T →ₗ[ℂ] CircleL2 T :=
  (1/2:ℂ) • (circleBlochCoefficient T h h₁ h₂ (j.castLE (by decide))+
    circleBlochAdjointCoefficient T h h₁ h₂ (j.castLE (by decide)))

theorem circle_bloch_symmetric_coefficient_zero (h h₁ h₂ : C(AddCircle T, ℂ))
    (f : circleH4Domain T) :
    circleBlochSymmetricCoefficient T h h₁ h₂ 0 f = circleH4SymmetricOperator T h h₁ h₂ f := by
  change (1/2:ℂ) • (circleH4Operator T h h₁ h₂ f+circleH4FormalAdjoint T h h₁ f) = _
  rw [circle_h4_formal_adjoint_split T h h₁ h₂]
  change (1/2:ℂ) • ((circleH4SymmetricOperator T h h₁ h₂ f+
    (15/2:ℂ) • (circleMultiplyL2 T h₁ (circleH4Jet T f).first+
      (1/2:ℂ) • circleMultiplyL2 T h₂ (f:CircleL2 T)))+
    (circleH4SymmetricOperator T h h₁ h₂ f-
      (15/2:ℂ) • (circleMultiplyL2 T h₁ (circleH4Jet T f).first+
        (1/2:ℂ) • circleMultiplyL2 T h₂ (f:CircleL2 T)))) = _
  module

theorem circle_bloch_symmetric_off_diagonal (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (CoarseArithmetic.fourierCoefficient CoarseArithmetic.thetaParameter CoarseArithmetic.nome j:ℂ))
    (j : Fin 3) (n m : ℤ) (hnm : n ≠ m) :
    fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*n) =
      (evenSymmetricOffScalar ((2*Real.pi/T)^2) j (2*(n:ℝ)) (2*(m:ℝ)):ℂ)*
        fourierCoeff h (2*n-2*m) := by
  have hne : 2*n ≠ 2*m := by omega
  have hne' : 2*m ≠ 2*n := Ne.symm hne
  have hc' : fourierCoeff h (2*m-2*n) = fourierCoeff h (2*n-2*m) := by
    rw [show 2*m-2*n = -(2*n-2*m) by ring,hs]
  have hcreal : conj (fourierCoeff h (2*n-2*m)) = fourierCoeff h (2*n-2*m) := by
    rw [show 2*n-2*m = 2*(n-m) by ring,
      circle_even_integer_coefficient T h CoarseArithmetic.thetaParameter CoarseArithmetic.nome hs hc]
    exact Complex.conj_ofReal _
  simp only [circleBlochSymmetricCoefficient,LinearMap.smul_apply,LinearMap.add_apply,
    circle_fourierCoeff_smul,circle_fourierCoeff_add,
    circle_bloch_coefficient_basis_fourier T h h₁ h₂ hh hh₁,
    circle_bloch_adjoint_basis_fourier T h h₁ h₂ hh hh₁ hreal h₁real h₂real]
  fin_cases j <;>
    norm_num only [circleBlochCoefficientEntry,evenSymmetricOffScalar,Fin.castLE,
      if_neg hne,if_neg hne',mul_zero,zero_add,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,hc',map_mul,Complex.conj_ofReal,hcreal]
  all_goals push_cast; ring

end Lemniscate
