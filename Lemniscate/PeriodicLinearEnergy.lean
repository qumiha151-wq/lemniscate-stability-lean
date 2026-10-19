import Lemniscate.PeriodicSkewEnergy

/-! Energy of the actual classical linearized expression printed in the paper.
The passage to the symmetric expression is proved by integration by parts,
including the first-order skew correction. Profile identification and the
unbounded-operator spectral theory remain separate obligations. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def paperLinearExpression (q p f f₁ f₂ f₄ : C(AddCircle T, ℂ)) :
    C(AddCircle T, ℂ) :=
  (-4:ℂ) • f₄ - (45:ℂ) • ((q^2)*f₂) - (75:ℂ) • (q*p*f₁) -
    (69/2:ℂ) • f - (45/2:ℂ) • ((q^4)*f)

theorem paper_linear_expression_split (q p f f₁ f₂ f₄ : C(AddCircle T, ℂ)) :
    paperLinearExpression T q p f f₁ f₂ f₄ =
      circleSymmetricExpression T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
        f f₁ f₂ f₄ + (15/2:ℂ) •
          (((2:ℂ) • (q*p))*f₁+(1/2:ℂ) • ((1-(3:ℂ) • (q^4))*f)) := by
  ext x
  change -4*f₄ x - 45*((q x)^2*f₂ x) - 75*(q x*p x*f₁ x) -
    (69/2:ℂ)*f x - (45/2:ℂ)*((q x)^4*f x) =
      (-4*f₄ x - 45*(2*(q x*p x)*f₁ x+(q x)^2*f₂ x) - 42*f x +
        (15/4:ℂ)*((1-3*(q x)^4)*f x)) +
          (15/2:ℂ)*(2*(q x*p x)*f₁ x+(1/2:ℂ)*((1-3*(q x)^4)*f x))
  ring

theorem paper_linear_classical_energy (q p f f₁ f₂ f₃ f₄ : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hreal : ∀ x, conj (q x*p x) = q x*p x)
    (hf : HasCircleDeriv T f f₁) (hf₁ : HasCircleDeriv T f₁ f₂)
    (hf₂ : HasCircleDeriv T f₂ f₃) (hf₃ : HasCircleDeriv T f₃ f₄) :
    (inner ℂ (circleContinuousL2 T f)
      (circleContinuousL2 T (paperLinearExpression T q p f f₁ f₂ f₄))).re =
      paperH2Energy T q (circleContinuousL2 T f) (circleContinuousL2 T f₁)
        (circleContinuousL2 T f₂) := by
  have hskew := circle_first_order_skew_energy T ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) f f₁ (circle_profile_square_second T q p hq hp he) hf (by
      intro x
      change conj (2*(q x*p x)) = 2*(q x*p x)
      simp only [map_mul, map_ofNat, hreal x])
  have hs := circle_classical_energy_eq T (q^2) ((2:ℂ) • (q*p))
    (1-(3:ℂ) • (q^4)) f f₁ f₂ f₃ f₄ (circle_profile_square_deriv T q p hq)
    hf hf₁ hf₂ hf₃
  rw [circle_h2_energy_profile] at hs
  rw [paper_linear_expression_split]
  have hl (a b : C(AddCircle T, ℂ)) :
      circleContinuousL2 T (a+(15/2:ℂ) • b) =
        circleContinuousL2 T a+(15/2:ℂ) • circleContinuousL2 T b := by
    simp only [circleContinuousL2, map_add, map_smul]
  rw [hl, inner_add_right, inner_smul_right, Complex.add_re, Complex.mul_re]
  norm_num
  simp only [smul_mul_assoc] at hskew
  rw [hskew, hs]
  ring

theorem paper_linear_classical_cosine_dissipative
    (q p f f₁ f₂ f₃ f₄ : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hreal : ∀ x, conj (q x*p x) = q x*p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter)
    (hf : HasCircleDeriv T f f₁) (hf₁ : HasCircleDeriv T f₁ f₂)
    (hf₂ : HasCircleDeriv T f₂ f₃) (hf₃ : HasCircleDeriv T f₃ f₄)
    (v : CosineSequenceSpace) (hv : circleContinuousL2 T f = circleEvenCosineSynthesis T v) :
    (inner ℂ (circleContinuousL2 T f)
      (circleContinuousL2 T (paperLinearExpression T q p f f₁ f₂ f₄))).re ≤
      -(21/4:ℝ)*‖circleContinuousL2 T f‖^2 := by
  rw [paper_linear_classical_energy T q p f f₁ f₂ f₃ f₄ hq hp he hreal hf hf₁ hf₂ hf₃]
  have hfu := circle_classical_weak_deriv T f f₁ hf
  have hug := circle_classical_weak_deriv T f₁ f₂ hf₁
  rw [hv] at hfu ⊢
  exact paper_cosine_weak_energy_dissipative T q p hq hp he hs hc hr v _ _ hfu hug

end Lemniscate
