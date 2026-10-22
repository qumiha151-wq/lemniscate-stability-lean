import Lemniscate.PeriodicSineFiniteEnergy
import Lemniscate.PeriodicSineApproximation

/-! Identify the entire H2 sine energy with the complete coefficient block
form and transfer its constrained -75 bound to arbitrary weak derivatives.
The Jacobi Fourier coefficients and period relation remain explicit hypotheses. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_block_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    circleH2Energy T h h₂ (circleSineBlockFunction T u v) (circleSineBlockFirst T u v hv)
      (circleSineBlockSecond T u v hv) = sineH2BlockForm u v := by
  have he := circle_h2_energy_tendsto T h h₂
    (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 0))
    (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 1))
    (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 2))
    (circleSineBlockFunction T u v) (circleSineBlockFirst T u v hv) (circleSineBlockSecond T u v hv)
    (circle_sine_block_polynomial_tendsto T u v)
    (circle_sine_block_polynomial_first_tendsto T u v hv)
    (circle_sine_block_polynomial_second_tendsto T u v hv)
  have hm : Tendsto (fun I : Finset ℕ =>
      circleH2Energy T h h₂ (circleContinuousL2 T (circleSinePolynomial T I u v 0))
        (circleContinuousL2 T (circleSinePolynomial T I u v 1))
        (circleContinuousL2 T (circleSinePolynomial T I u v 2)))
      atTop (𝓝 (sineH2BlockForm u v)) := by
    simpa only [circle_sine_polynomial_h2_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr] using
      sine_finite_block_form_tendsto u v hv
  exact tendsto_nhds_unique he hm

theorem circle_sine_weak_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (u : ℂ) (v : SineTailSpace)
    (f₁ f₂ : CircleL2 T) (hf : HasWeakCircleDeriv T (circleSineBlockFunction T u v) f₁)
    (hf₁ : HasWeakCircleDeriv T f₁ f₂) :
    circleH2Energy T h h₂ (circleSineBlockFunction T u v) f₁ f₂ = sineH2BlockForm u v := by
  have hv : HasSineTailH2Coefficients v :=
    (circle_sine_block_mem_h2_iff T u v).mp ⟨f₁, f₂, hf, hf₁⟩
  have hfirst : f₁ = circleSineBlockFirst T u v hv :=
    weak_circle_deriv_unique T _ _ _ hf (circle_sine_block_derivative_chain T u v hv).1
  have hsecond : f₂ = circleSineBlockSecond T u v hv :=
    weak_circle_second_unique T _ _ _
      (weak_circle_second_of_deriv_chain T _ _ _ hf hf₁) (circle_sine_block_second_weak T u v hv)
  rw [hfirst, hsecond]
  exact circle_sine_block_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr u v hv

theorem circle_sine_weak_energy_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (u : ℂ) (v : SineTailSpace)
    (f₁ f₂ : CircleL2 T) (hf : HasWeakCircleDeriv T (circleSineBlockFunction T u v) f₁)
    (hf₁ : HasWeakCircleDeriv T f₁ f₂)
    (horth : inner ℂ (circleSineConstraintVector T) (circleSineBlockFunction T u v) = 0) :
    circleH2Energy T h h₂ (circleSineBlockFunction T u v) f₁ f₂ ≤
      -75*‖circleSineBlockFunction T u v‖^2 := by
  rw [circle_sine_weak_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr u v f₁ f₂ hf hf₁]
  exact circle_sine_sobolev_constrained_coefficient_energy T u v ⟨f₁, f₂, hf, hf₁⟩ horth

end Lemniscate
