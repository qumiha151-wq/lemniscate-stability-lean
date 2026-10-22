import Lemniscate.PeriodicSinePolynomials
import Lemniscate.PeriodicSineBlockH2
import Lemniscate.PeriodicDerivativeGraph

/-! Simultaneous approximation of the sine block and its first two actual
weak derivatives. No fourth derivative of the limiting function is required. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSineSecondFactor (j : ℕ) : ℂ :=
  ((-((2*Real.pi/T)^2*(2*((j:ℝ)+1))^2):ℝ):ℂ)

theorem circle_sine_jet_second (j : ℕ) :
    circleSineJet T j 2 = circleSineSecondFactor T j • circleSineJet T j 0 := by
  simp only [circleSineJet, pow_zero, one_smul, circle_frequency_factor_sq,
    Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
    Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_one, neg_sq]
  ext x
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul,
    circleSineSecondFactor]
  push_cast
  ring

theorem circle_sine_polynomial_second_l2 (I : Finset ℕ) (u : ℂ) (v : ℕ → ℂ) :
    circleContinuousL2 T (circleSinePolynomial T I u v 2) =
      u • (circleSineSecondFactor T 0 • circleEvenSineMode T 0) +
      (((2*Real.pi/T)^2:ℝ):ℂ) •
        ∑ j ∈ I, sineSecondCoefficients 2 v j • circleEvenSineMode T (j+1) := by
  simp only [circleSinePolynomial, circle_continuous_l2_add, circle_continuous_l2_sum,
    circle_continuous_l2_smul, circle_sine_jet_second, circle_sine_jet_zero_l2,
    Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  unfold sineSecondCoefficients circleSineSecondFactor
  push_cast
  ring

noncomputable def circleSineBlockSecond (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) : CircleL2 T :=
  u • (circleSineSecondFactor T 0 • circleEvenSineMode T 0) +
    (((2*Real.pi/T)^2:ℝ):ℂ) •
      circleSineTailSynthesis T (sineSecondSequence 2 v ((sine_tail_h2_iff v).mp hv))

theorem circle_sine_block_second_weak (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    HasWeakCircleSecond T (circleSineBlockFunction T u v) (circleSineBlockSecond T u v hv) :=
  circle_weak_second_add T _ _ _ _
    (circle_weak_second_smul T u _ _ (circle_sine_mode_weak_second T 0))
    (circle_sine_tail_weak_second T v ((sine_tail_h2_iff v).mp hv))

noncomputable def circleSineBlockFirst (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) : CircleL2 T :=
  circleFirstFromSecond T (circleSineBlockFunction T u v) (circleSineBlockSecond T u v hv)
    (circle_sine_block_second_weak T u v hv)

theorem circle_sine_block_derivative_chain (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    HasWeakCircleDeriv T (circleSineBlockFunction T u v) (circleSineBlockFirst T u v hv) ∧
      HasWeakCircleDeriv T (circleSineBlockFirst T u v hv) (circleSineBlockSecond T u v hv) :=
  ⟨circle_first_from_second_weak T _ _ (circle_sine_block_second_weak T u v hv),
    circle_first_from_second_deriv T _ _ (circle_sine_block_second_weak T u v hv)⟩

theorem circle_sine_block_polynomial_tendsto (u : ℂ) (v : SineTailSpace) :
    Tendsto (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 0))
      atTop (𝓝 (circleSineBlockFunction T u v)) := by
  have hs : Tendsto (fun I : Finset ℕ => ∑ j ∈ I, v j • circleEvenSineMode T (j+1))
      atTop (𝓝 (circleSineTailSynthesis T v)) := circle_sine_tail_hasSum T v
  simpa only [circle_sine_polynomial_l2, circleSineBlockFunction] using
    hs.const_add (u • circleEvenSineMode T 0)

theorem circle_sine_block_polynomial_second_tendsto (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 2))
      atTop (𝓝 (circleSineBlockSecond T u v hv)) := by
  have hs : Tendsto (fun I : Finset ℕ =>
      ∑ j ∈ I, sineSecondCoefficients 2 v j • circleEvenSineMode T (j+1))
      atTop (𝓝 (circleSineTailSynthesis T (sineSecondSequence 2 v ((sine_tail_h2_iff v).mp hv)))) :=
    circle_sine_tail_hasSum T (sineSecondSequence 2 v ((sine_tail_h2_iff v).mp hv))
  simpa only [circle_sine_polynomial_second_l2, circleSineBlockSecond] using
    (hs.const_smul ((((2*Real.pi/T)^2:ℝ):ℂ))).const_add
      (u • (circleSineSecondFactor T 0 • circleEvenSineMode T 0))

theorem circle_sine_block_polynomial_first_tendsto (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v) :
    Tendsto (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 1))
      atTop (𝓝 (circleSineBlockFirst T u v hv)) := by
  apply circle_first_derivative_tendsto T
    (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 0))
    (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 1))
    (fun I : Finset ℕ => circleContinuousL2 T (circleSinePolynomial T I u v 2))
    (circleSineBlockFunction T u v) (circleSineBlockFirst T u v hv) (circleSineBlockSecond T u v hv)
  · intro I
    exact circle_classical_weak_deriv T _ _ (circle_sine_polynomial_deriv T I u v 0)
  · intro I
    exact circle_classical_weak_deriv T _ _ (circle_sine_polynomial_deriv T I u v 1)
  · exact (circle_sine_block_derivative_chain T u v hv).1
  · exact (circle_sine_block_derivative_chain T u v hv).2
  · exact circle_sine_block_polynomial_tendsto T u v
  · exact circle_sine_block_polynomial_second_tendsto T u v hv

end Lemniscate
