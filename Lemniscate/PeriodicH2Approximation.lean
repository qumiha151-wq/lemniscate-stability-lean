import Lemniscate.PeriodicDerivativeGraph

/-! Finite cosine polynomials converge simultaneously with both weak
derivatives in the actual L2 space. No convergence of a fourth derivative is
required for this H2 approximation. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

theorem circle_cosine_jet_second (j : ℕ) :
    circleCosineJet T j 2 =
      ((-((2*Real.pi/T)^2*(2*(j:ℝ))^2):ℝ):ℂ) • circleCosineJet T j 0 := by
  by_cases hj : j = 0
  · subst j
    simp [circleCosineJet, circleFrequencyFactor]
  · simp only [circleCosineJet, if_neg hj, pow_zero, one_smul,
      circle_frequency_factor_sq, Int.cast_neg, Int.cast_mul, Int.cast_ofNat,
      Int.cast_natCast, neg_sq]
    ext x
    simp only [ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul]
    push_cast
    ring

theorem circle_cosine_polynomial_second_l2 (I : Finset ℕ) (v : ℕ → ℂ) :
    circleContinuousL2 T (circleCosinePolynomial T I v 2) =
      (((2*Real.pi/T)^2:ℝ):ℂ) •
        ∑ j ∈ I, evenSecondCoefficients v j • circleEvenCosineMode T j := by
  simp only [circleCosinePolynomial, circle_continuous_l2_sum,
    circle_continuous_l2_smul, circle_cosine_jet_second, circle_cosine_jet_zero_l2,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold evenSecondCoefficients
  push_cast
  ring

theorem h2_circle_polynomial_tendsto (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 0))
      atTop (𝓝 (h2CircleFunction T v hv)) := by
  simp only [circle_cosine_polynomial_l2]
  exact circle_even_cosine_hasSum T (h2Sequence v hv)

theorem h2_circle_polynomial_second_tendsto (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 2))
      atTop (𝓝 (h2CircleSecond T v hv)) := by
  have hs : Tendsto (fun I : Finset ℕ =>
      ∑ j ∈ I, evenSecondCoefficients v j • circleEvenCosineMode T j)
      atTop (𝓝 (h2CircleAngularSecond T v hv)) := h2_circle_angular_second_hasSum T v hv
  simpa only [circle_cosine_polynomial_second_l2, h2CircleSecond] using
    hs.const_smul ((((2*Real.pi/T)^2:ℝ):ℂ))

theorem h2_circle_polynomial_first_tendsto (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 1))
      atTop (𝓝 (h2CircleFirst T v hv)) := by
  apply circle_first_derivative_tendsto T
    (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 0))
    (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 1))
    (fun I : Finset ℕ => circleContinuousL2 T (circleCosinePolynomial T I v 2))
    (h2CircleFunction T v hv) (h2CircleFirst T v hv) (h2CircleSecond T v hv)
  · intro I
    exact circle_classical_weak_deriv T _ _ (circle_cosine_polynomial_deriv T I v 0)
  · intro I
    exact circle_classical_weak_deriv T _ _ (circle_cosine_polynomial_deriv T I v 1)
  · exact (h2_circle_derivative_chain T v hv).1
  · exact (h2_circle_derivative_chain T v hv).2
  · exact h2_circle_polynomial_tendsto T v hv
  · exact h2_circle_polynomial_second_tendsto T v hv

end Lemniscate
