import Lemniscate.PeriodicOddApproximation

/-! Identification of the infinite odd coefficient form with the actual
periodic H2 energy, retaining the explicit profile Fourier and period data. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic OddArithmetic Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

theorem circle_odd_weak_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f f₁ f₂ : CircleL2 T)
    (hf : InCircleOddSector T f) (hff₁ : HasWeakCircleDeriv T f f₁)
    (hf₁f₂ : HasWeakCircleDeriv T f₁ f₂) :
    circleH2Energy T h h₂ f f₁ f₂ =
      oddH2Form 0 (fun i : ℤ => fourierCoeff f (2*i+1)) := by
  let v : ℤ → ℂ := fun i => fourierCoeff f (2*i+1)
  have hv : HasOddH2Coefficients v := circle_odd_h2_coefficients T f ⟨f₁, f₂, hff₁, hf₁f₂⟩ hr
  have he := circle_h2_energy_tendsto T h h₂
    (fun I : Finset ℤ => circleContinuousL2 T (circleOddPolynomial T I v 0))
    (fun I : Finset ℤ => circleContinuousL2 T (circleOddPolynomial T I v 1))
    (fun I : Finset ℤ => circleContinuousL2 T (circleOddPolynomial T I v 2)) f f₁ f₂
    (circle_odd_polynomial_tendsto T f hf)
    (circle_odd_polynomial_first_tendsto T f f₁ hf hff₁)
    (circle_odd_polynomial_second_tendsto T f f₁ f₂ hf hff₁ hf₁f₂)
  have hm : Tendsto (fun I : Finset ℤ =>
      circleH2Energy T h h₂ (circleContinuousL2 T (circleOddPolynomial T I v 0))
        (circleContinuousL2 T (circleOddPolynomial T I v 1))
        (circleContinuousL2 T (circleOddPolynomial T I v 2))) atTop (𝓝 (oddH2Form 0 v)) := by
    simpa only [circle_odd_polynomial_h2_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr,
      oddH2Form, Function.comp_def] using (Complex.continuous_re.tendsto _).comp
        (odd_energy_tendsto v hv 0 (by norm_num) (by norm_num))
  exact tendsto_nhds_unique he hm

theorem circle_odd_weak_energy_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (f f₁ f₂ : CircleL2 T)
    (hf : InCircleOddSector T f) (hff₁ : HasWeakCircleDeriv T f f₁)
    (hf₁f₂ : HasWeakCircleDeriv T f₁ f₂) :
    circleH2Energy T h h₂ f f₁ f₂ ≤ -6*‖f‖^2 := by
  rw [circle_odd_weak_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr f f₁ f₂ hf hff₁ hf₁f₂,
    circle_odd_norm_sq T f hf]
  exact odd_zero_h2_form_dissipative _
    (circle_odd_h2_coefficients T f ⟨f₁, f₂, hff₁, hf₁f₂⟩ hr)

end Lemniscate
