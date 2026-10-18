import Lemniscate.PeriodicProfileIdentity

/-! The classical fourth-order differential expression used for the symmetric
part in the paper. Its identification as an operator adjoint on a Sobolev domain
is a separate obligation. Here we check derivatives and its Fourier matrix. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSymmetricExpression (h h₁ h₂ f f₁ f₂ f₄ : C(AddCircle T, ℂ)) :
    C(AddCircle T, ℂ) :=
  (-4:ℂ) • f₄ - (45:ℂ) • (h₁*f₁+h*f₂) - (42:ℂ) • f + (15/4:ℂ) • (h₂*f)

theorem circle_symmetric_expression_coordinate
    (h h₁ h₂ f f₁ f₂ f₃ f₄ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hf : HasCircleDeriv T f f₁)
    (hf₁ : HasCircleDeriv T f₁ f₂) (hf₂ : HasCircleDeriv T f₂ f₃)
    (hf₃ : HasCircleDeriv T f₃ f₄) (x : ℝ) :
    circleSymmetricExpression T h h₁ h₂ f f₁ f₂ f₄ (x:AddCircle T) =
      -4*deriv (deriv (deriv (deriv (fun y : ℝ => f (y:AddCircle T))))) x -
      45*deriv (fun y : ℝ => h (y:AddCircle T)*
        deriv (fun z : ℝ => f (z:AddCircle T)) y) x -
      42*f (x:AddCircle T) + (15/4:ℂ)*h₂ (x:AddCircle T)*f (x:AddCircle T) := by
  have d₀ : deriv (fun y : ℝ => f (y:AddCircle T)) = fun y : ℝ => f₁ (y:AddCircle T) :=
    funext fun y => (hf y).deriv
  have d₁ : deriv (fun y : ℝ => f₁ (y:AddCircle T)) = fun y : ℝ => f₂ (y:AddCircle T) :=
    funext fun y => (hf₁ y).deriv
  have d₂ : deriv (fun y : ℝ => f₂ (y:AddCircle T)) = fun y : ℝ => f₃ (y:AddCircle T) :=
    funext fun y => (hf₂ y).deriv
  have d₃ : deriv (fun y : ℝ => f₃ (y:AddCircle T)) = fun y : ℝ => f₄ (y:AddCircle T) :=
    funext fun y => (hf₃ y).deriv
  have dp : deriv (fun y : ℝ => h (y:AddCircle T)*f₁ (y:AddCircle T)) x =
      h₁ (x:AddCircle T)*f₁ (x:AddCircle T) + h (x:AddCircle T)*f₂ (x:AddCircle T) := by
    simpa only [Pi.mul_def] using ((hh x).mul (hf₁ x)).deriv
  rw [d₀, d₁, d₂, d₃, dp]
  change -4*f₄ (x:AddCircle T) - 45*(h₁ (x:AddCircle T)*f₁ (x:AddCircle T) +
      h (x:AddCircle T)*f₂ (x:AddCircle T)) - 42*f (x:AddCircle T) +
      (15/4:ℂ)*(h₂ (x:AddCircle T)*f (x:AddCircle T)) = _
  ring

theorem circle_fourier_derivative_power (m : ℤ) (k : ℕ) :
    HasCircleDeriv T ((circleFrequencyFactor T m)^k • fourier m)
      ((circleFrequencyFactor T m)^(k+1) • fourier m) := by
  intro x
  convert! (hasDerivAt_circle_fourier T m x).const_mul ((circleFrequencyFactor T m)^k)
    using 1
  change (circleFrequencyFactor T m)^(k+1) * fourier m (x:AddCircle T) = _
  rw [pow_succ]
  ring

theorem circle_frequency_factor_mul (n m : ℤ) :
    circleFrequencyFactor T n * circleFrequencyFactor T m =
      ((-((2*Real.pi/T)^2*(n:ℝ)*(m:ℝ)):ℝ):ℂ) := by
  unfold circleFrequencyFactor
  push_cast
  calc
    _ = ((2*(Real.pi:ℂ)/T)^2*(n:ℂ)*(m:ℂ))*I^2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

theorem circle_frequency_factor_fourth (m : ℤ) :
    (circleFrequencyFactor T m)^4 = (((2*Real.pi/T)^4*(m:ℝ)^4:ℝ):ℂ) := by
  calc
    _ = ((circleFrequencyFactor T m)^2)^2 := by ring
    _ = _ := by rw [circle_frequency_factor_sq]; push_cast; ring

noncomputable def circleSymmetricMode (h h₁ h₂ : C(AddCircle T, ℂ)) (m : ℤ) :
    C(AddCircle T, ℂ) :=
  circleSymmetricExpression T h h₁ h₂ (fourier m)
    (circleFrequencyFactor T m • fourier m)
    ((circleFrequencyFactor T m)^2 • fourier m)
    ((circleFrequencyFactor T m)^4 • fourier m)

noncomputable def circleSymmetricFourierEntry (h : C(AddCircle T, ℂ)) (n m : ℤ) : ℂ :=
  ((-4*(2*Real.pi/T)^4*(m:ℝ)^4-42:ℝ):ℂ)*(if n = m then 1 else 0) +
  (((2*Real.pi/T)^2*(45*(n:ℝ)*(m:ℝ)-(15/4:ℝ)*((n:ℝ)-(m:ℝ))^2):ℝ):ℂ)*
    fourierCoeff h (n-m)

theorem circle_symmetric_mode_fourier (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂) (n m : ℤ) :
    fourierCoeff (circleSymmetricMode T h h₁ h₂ m) n =
      circleSymmetricFourierEntry T h n m := by
  simp only [circleSymmetricMode, circleSymmetricExpression,
    circle_continuous_fourier_add, circle_continuous_fourier_sub,
    circle_continuous_fourier_smul, circle_fourier_product_smul_mode,
    circle_fourier_product_mode, circle_continuous_fourier_mode]
  rw [fourierCoeff_classical_deriv T h h₁ hh,
    fourierCoeff_classical_second T h h₁ h₂ hh hh₁]
  calc
    _ = (-4*(circleFrequencyFactor T m)^4-42)*(if n = m then 1 else 0) +
        (-45*(circleFrequencyFactor T m * circleFrequencyFactor T (n-m) +
            (circleFrequencyFactor T m)^2) +
          (15/4:ℂ)*((-((2*Real.pi/T)^2*((n-m:ℤ):ℝ)^2):ℝ):ℂ))*
            fourierCoeff h (n-m) := by ring
    _ = _ := by
      rw [circle_frequency_factor_fourth, circle_frequency_factor_mul,
        circle_frequency_factor_sq]
      unfold circleSymmetricFourierEntry
      push_cast
      ring

noncomputable def paperSymmetricExpression (q p f f₁ f₂ f₄ : C(AddCircle T, ℂ)) :
    C(AddCircle T, ℂ) :=
  (-4:ℂ) • f₄ - (45:ℂ) • ((q^2)*f₂ + (2:ℂ) • (q*p*f₁)) -
    (153/4:ℂ) • f - (45/4:ℂ) • ((q^4)*f)

theorem circle_symmetric_expression_profile (q p f f₁ f₂ f₄ : C(AddCircle T, ℂ)) :
    circleSymmetricExpression T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
      f f₁ f₂ f₄ = paperSymmetricExpression T q p f f₁ f₂ f₄ := by
  ext x
  change -4*f₄ x - 45*(2*(q x*p x)*f₁ x+(q x)^2*f₂ x) - 42*f x +
    (15/4:ℂ)*((1-3*(q x)^4)*f x) =
      -4*f₄ x - 45*((q x)^2*f₂ x+2*(q x*p x*f₁ x)) -
        (153/4:ℂ)*f x - (45/4:ℂ)*((q x)^4*f x)
  ring

theorem paper_symmetric_mode_fourier (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1) (n m : ℤ) :
    fourierCoeff (paperSymmetricExpression T q p (fourier m)
      (circleFrequencyFactor T m • fourier m)
      ((circleFrequencyFactor T m)^2 • fourier m)
      ((circleFrequencyFactor T m)^4 • fourier m)) n =
        circleSymmetricFourierEntry T (q^2) n m := by
  rw [← circle_symmetric_expression_profile]
  exact circle_symmetric_mode_fourier T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4))
    (circle_profile_square_deriv T q p hq) (circle_profile_square_second T q p hq hp he) n m

end Lemniscate
