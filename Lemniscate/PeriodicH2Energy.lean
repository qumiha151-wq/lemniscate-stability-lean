import Lemniscate.PeriodicH2Approximation

/-! Identify the actual H2 variational energy with the absolutely convergent
coefficient form and transfer the certified dissipation bound to weak
derivatives. The Jacobi/theta coefficient identity is still an explicit hypothesis. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

theorem h2_circle_energy_eq_coefficients (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    circleH2Energy T h h₂ (h2CircleFunction T v hv) (h2CircleFirst T v hv)
      (h2CircleSecond T v hv) = cosineH2Form v := by
  have he := circle_h2_energy_tendsto T h h₂
    (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 0))
    (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 1))
    (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 2))
    (h2CircleFunction T v hv) (h2CircleFirst T v hv) (h2CircleSecond T v hv)
    (h2_circle_polynomial_tendsto T v hv) (h2_circle_polynomial_first_tendsto T v hv)
    (h2_circle_polynomial_second_tendsto T v hv)
  have hm : Tendsto (fun I : Finset ℕ =>
      circleH2Energy T h h₂ (circleContinuousL2 T (circleCosinePolynomial T I v 0))
        (circleContinuousL2 T (circleCosinePolynomial T I v 1))
        (circleContinuousL2 T (circleCosinePolynomial T I v 2)))
      atTop (𝓝 (cosineH2Form v)) := by
    have hc₀ := (Complex.continuous_re.tendsto _).comp (cosine_energy_tendsto v hv)
    convert! hc₀ using 1
    funext I
    rw [circle_polynomial_h2_energy_eq T h h₁ h₂ hh,
      circle_polynomial_energy_eq_matrix T h h₁ h₂ thetaParameter nome hh hh₁ hs hc hr]
    rfl
  exact tendsto_nhds_unique he hm

theorem h2_circle_energy_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    circleH2Energy T h h₂ (h2CircleFunction T v hv) (h2CircleFirst T v hv)
      (h2CircleSecond T v hv) ≤ -(21/4:ℝ)*‖h2CircleFunction T v hv‖^2 := by
  rw [h2_circle_energy_eq_coefficients T h h₁ h₂ hh hh₁ hs hc hr]
  exact h2_circle_function_energy_bound T v hv

theorem circle_cosine_weak_energy_dissipative (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) = (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 = thetaParameter) (v : CosineSequenceSpace) (u g : CircleL2 T)
    (hfu : HasWeakCircleDeriv T (circleEvenCosineSynthesis T v) u)
    (hug : HasWeakCircleDeriv T u g) :
    circleH2Energy T h h₂ (circleEvenCosineSynthesis T v) u g ≤
      -(21/4:ℝ)*‖circleEvenCosineSynthesis T v‖^2 := by
  have hv : HasH2Coefficients (fun j => v j) :=
    (circle_cosine_mem_h2_iff T v).mp ⟨u, g, hfu, hug⟩
  have hf : h2CircleFunction T (fun j => v j) hv = circleEvenCosineSynthesis T v := by
    unfold h2CircleFunction
    congr 1
  have hchain := h2_circle_derivative_chain T (fun j => v j) hv
  rw [hf] at hchain
  have hu : u = h2CircleFirst T (fun j => v j) hv :=
    weak_circle_deriv_unique T _ _ _ hfu hchain.1
  have hg : g = h2CircleSecond T (fun j => v j) hv :=
    weak_circle_deriv_unique T u g _ hug (by simpa only [← hu] using hchain.2)
  rw [hu, hg, ← hf]
  exact h2_circle_energy_dissipative T h h₁ h₂ hh hh₁ hs hc hr _ hv

end Lemniscate
