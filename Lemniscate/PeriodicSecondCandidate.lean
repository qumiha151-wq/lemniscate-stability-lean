import Lemniscate.CosineSecondCoefficients

/-! Construction and convergence of the angular second-derivative candidate.
This file proves the complete Fourier multiplier identity and symmetry of the
candidate. Identification with weak derivatives is a separate next step. -/
namespace Lemniscate
open CoarseArithmetic Complex Filter
open scoped Topology ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

noncomputable def h2CircleAngularSecond (v : ℕ → ℂ) (hv : HasH2Coefficients v) : CircleL2 T :=
  circleEvenCosineSynthesis T (evenSecondSequence v hv)

theorem h2_circle_angular_second_hasSum (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    HasSum (fun j : ℕ => evenSecondCoefficients v j • circleEvenCosineMode T j)
      (h2CircleAngularSecond T v hv) :=
  circle_even_cosine_hasSum T (evenSecondSequence v hv)

theorem h2_circle_angular_second_norm_sq (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    ‖h2CircleAngularSecond T v hv‖^2 =
      ∑' j : ℕ, ((2*(j:ℝ))^2*‖v j‖)^2 := by
  simpa only [h2CircleAngularSecond, evenSecondSequence, even_second_coefficient_norm] using
    circle_even_cosine_norm_sq T (evenSecondSequence v hv)

theorem circle_mode_second_multiplier (j : ℕ) (n : ℤ) :
    ((-(2*(j:ℝ))^2 : ℝ):ℂ) * fourierCoeff (circleEvenCosineMode T j) n =
      ((-(n:ℝ)^2 : ℝ):ℂ) * fourierCoeff (circleEvenCosineMode T j) n := by
  rw [circle_even_cosine_mode_coeff]
  by_cases hj : j = 0
  · subst j
    by_cases hn : n = 0 <;> simp [hn]
  · by_cases hp : n = 2*(j:ℤ)
    · subst n
      simp only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
    · by_cases hn : n = -(2*(j:ℤ))
      · subst n
        simp only [Int.cast_neg, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, neg_sq]
      · simp [hj, hp, hn]

theorem h2_circle_angular_second_fourier (v : ℕ → ℂ) (hv : HasH2Coefficients v) (n : ℤ) :
    fourierCoeff (h2CircleAngularSecond T v hv) n =
      ((-(n:ℝ)^2 : ℝ):ℂ) * fourierCoeff (h2CircleFunction T v hv) n := by
  have h := (circle_even_cosine_coeff_hasSum T (h2Sequence v hv) n).mul_left
    (((-(n:ℝ)^2 : ℝ):ℂ))
  apply (circle_even_cosine_coeff_hasSum T (evenSecondSequence v hv) n).unique
  convert! h using 1
  ext j
  change evenSecondCoefficients v j * fourierCoeff (circleEvenCosineMode T j) n =
    ((-(n:ℝ)^2 : ℝ):ℂ) * (v j * fourierCoeff (circleEvenCosineMode T j) n)
  calc
    _ = v j * (((-(2*(j:ℝ))^2 : ℝ):ℂ) *
        fourierCoeff (circleEvenCosineMode T j) n) := by unfold evenSecondCoefficients; ring
    _ = v j * (((-(n:ℝ)^2 : ℝ):ℂ) *
        fourierCoeff (circleEvenCosineMode T j) n) := by rw [circle_mode_second_multiplier]
    _ = _ := by ring

noncomputable def circleCosinePartial (v : ℕ → ℂ) (N : ℕ) : CircleL2 T :=
  ∑ j ∈ Finset.range N, v j • circleEvenCosineMode T j

theorem h2_circle_partial_tendsto (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (circleCosinePartial T v) atTop (𝓝 (h2CircleFunction T v hv)) :=
  (circle_even_cosine_hasSum T (h2Sequence v hv)).tendsto_sum_nat

theorem h2_circle_second_partial_tendsto (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (circleCosinePartial T (evenSecondCoefficients v)) atTop
      (𝓝 (h2CircleAngularSecond T v hv)) :=
  (h2_circle_angular_second_hasSum T v hv).tendsto_sum_nat

theorem h2_circle_graph_approximation (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Tendsto (fun N : ℕ => ‖circleCosinePartial T v N - h2CircleFunction T v hv‖ +
      ‖circleCosinePartial T (evenSecondCoefficients v) N - h2CircleAngularSecond T v hv‖)
      atTop (𝓝 0) := by
  have h₁ := ((h2_circle_partial_tendsto T v hv).sub_const (h2CircleFunction T v hv)).norm
  have h₂ := ((h2_circle_second_partial_tendsto T v hv).sub_const
    (h2CircleAngularSecond T v hv)).norm
  simpa using h₁.add h₂

theorem h2_circle_angular_second_symmetric (v w : ℕ → ℂ)
    (hv : HasH2Coefficients v) (hw : HasH2Coefficients w) :
    inner ℂ (h2CircleAngularSecond T v hv) (h2CircleFunction T w hw) =
      inner ℂ (h2CircleFunction T v hv) (h2CircleAngularSecond T w hw) := by
  change inner ℂ (circleEvenCosineSynthesis T (evenSecondSequence v hv))
      (circleEvenCosineSynthesis T (h2Sequence w hw)) =
    inner ℂ (circleEvenCosineSynthesis T (h2Sequence v hv))
      (circleEvenCosineSynthesis T (evenSecondSequence w hw))
  rw [(circleEvenCosineSynthesis T).inner_map_map, (circleEvenCosineSynthesis T).inner_map_map,
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℂ (evenSecondCoefficients v j) (w j) =
    inner ℂ (v j) (evenSecondCoefficients w j)
  simp only [evenSecondCoefficients, RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

end Lemniscate
