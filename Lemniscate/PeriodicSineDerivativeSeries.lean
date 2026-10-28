import Lemniscate.PeriodicSineDerivativeNorm

/-! Absolutely convergent sine expansions identify all actual weak derivatives.
Their omitted tails bound the error of finite Fourier truncation. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sine_derivative_hasSum (f : circleH4Domain T) (v : SineSequenceSpace)
    (hf : (f : CircleL2 T) = circleEvenSineSynthesis T v) (j : Fin 4)
    (hv : Summable (fun n : ℕ => ‖v n‖ *
      (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^(j.val+1))) :
    HasSum (fun n : ℕ => v n • circleH4Derivative T j (circleSineH4 T n))
      (circleH4Derivative T j f) := by
  have hn : Summable (fun n : ℕ => ‖v n • circleH4Derivative T j (circleSineH4 T n)‖) := by
    simpa only [norm_smul,circle_sine_h4_derivative_norm] using hv
  have hs := hn.of_norm.hasSum
  have heq : (∑' n : ℕ, v n • circleH4Derivative T j (circleSineH4 T n)) =
      circleH4Derivative T j f := by
    apply circle_fourier_ext T
    intro m
    have hsum := hs.mapL (innerSL ℂ (fourierBasis (T := T) m))
    simp only [innerSL_apply_apply,inner_smul_right,
      ← HilbertBasis.repr_apply_apply,fourierBasis_repr,circle_h4_derivative_fourier] at hsum
    have hbase := (circle_even_sine_coeff_hasSum T v m).mul_right
      ((circleFrequencyFactor T m)^(j.val+1))
    rw [circle_h4_derivative_fourier,hf]
    apply hsum.unique
    change HasSum (fun n : ℕ => v n * (fourierCoeff (circleEvenSineMode T n) m *
      (circleFrequencyFactor T m)^(j.val+1))) _
    simpa only [mul_assoc] using hbase
  rwa [heq] at hs

private theorem norm_series_tail (a : ℕ → CircleL2 T) (b : CircleL2 T)
    (hs : HasSum a b) (ha : Summable (fun n => ‖a n‖)) (N : ℕ) :
    ‖b-∑ n : Fin N, a n.val‖ ≤ ∑' n : ℕ, ‖a (n+N)‖ := by
  have heq := hs.summable.sum_add_tsum_nat_add N
  rw [hs.tsum_eq,← Fin.sum_univ_eq_sum_range] at heq
  have htail : b-∑ n : Fin N, a n.val = ∑' n : ℕ, a (n+N) := by
    rw [← heq]
    abel
  rw [htail]
  exact norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr ha)

theorem circle_sine_truncation_l2_error (v : SineSequenceSpace)
    (hv : Summable (fun n : ℕ => ‖v n‖)) (N : ℕ) :
    ‖circleEvenSineSynthesis T v-
      (circleSineTrialH4 T N (fun n => v n.val) : CircleL2 T)‖ ≤
        ∑' n : ℕ, ‖v (n+N)‖ := by
  have hn (n : ℕ) : ‖v n • circleEvenSineMode T n‖ = ‖v n‖ := by
    rw [norm_smul,(circle_even_sine_orthonormal T).norm_eq_one,mul_one]
  have h := norm_series_tail T _ _ (circle_even_sine_hasSum T v)
    (by simpa only [hn] using hv) N
  simp only [circleSineTrialH4,Submodule.coe_sum,Submodule.coe_smul_of_tower]
  change ‖circleEvenSineSynthesis T v-
    ∑ n : Fin N, v n.val • circleEvenSineMode T n.val‖ ≤ _
  simpa only [hn] using h

theorem circle_sine_truncation_derivative_error (f : circleH4Domain T) (v : SineSequenceSpace)
    (hf : (f : CircleL2 T) = circleEvenSineSynthesis T v) (j : Fin 4)
    (hv : Summable (fun n : ℕ => ‖v n‖ *
      (2*Real.pi/T*(2*(n+1:ℕ):ℝ))^(j.val+1))) (N : ℕ) :
    ‖circleH4Derivative T j (f-circleSineTrialH4 T N (fun n => v n.val))‖ ≤
      ∑' n : ℕ, ‖v (n+N)‖ * (2*Real.pi/T*(2*(n+N+1:ℕ):ℝ))^(j.val+1) := by
  have hs := circle_sine_derivative_hasSum T f v hf j hv
  have h := norm_series_tail T _ _ hs (by
    simpa only [norm_smul,circle_sine_h4_derivative_norm] using hv) N
  simpa only [map_sub,circleSineTrialH4,map_sum,map_smul,
    norm_smul,circle_sine_h4_derivative_norm] using h

end Lemniscate
