import Lemniscate.PeriodicCosineCoefficients

/-! The H2 coefficient condition is exactly the graph domain of the second
frequency multiplier. The multiplier here differentiates the angular variable
zeta (period 2*pi); the physical circle coordinate includes an additional scale. -/
namespace Lemniscate
open CoarseArithmetic
open scoped ENNReal

noncomputable def evenSecondCoefficients (v : ℕ → ℂ) (j : ℕ) : ℂ :=
  ((-(2*(j:ℝ))^2 : ℝ):ℂ) * v j

theorem even_second_coefficient_norm (v : ℕ → ℂ) (j : ℕ) :
    ‖evenSecondCoefficients v j‖ = (2*(j:ℝ))^2 * ‖v j‖ := by
  simp only [evenSecondCoefficients, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg (sq_nonneg (2*(j:ℝ)))]

theorem h2_second_coefficients_summable (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Summable (fun j : ℕ => ‖evenSecondCoefficients v j‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    ((h2_coefficients_iff_even_frequency v).mp hv)
  intro j
  rw [even_second_coefficient_norm]
  apply pow_le_pow_left₀ (by positivity) _ 2
  exact mul_le_mul_of_nonneg_right (by linarith : (2*(j:ℝ))^2 ≤ 1+(2*(j:ℝ))^2)
    (norm_nonneg _)

theorem h2_second_coefficients_mem_l2 (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    Memℓp (evenSecondCoefficients v) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa [Real.rpow_two] using h2_second_coefficients_summable v hv

theorem h2_coefficients_iff_second_l2 (v : ℕ → ℂ) :
    HasH2Coefficients v ↔ Memℓp v 2 ∧ Memℓp (evenSecondCoefficients v) 2 := by
  constructor
  · intro hv
    exact ⟨h2_coefficients_mem_l2 v hv, h2_second_coefficients_mem_l2 v hv⟩
  · rintro ⟨hv, hd⟩
    have hm : Summable (fun j : ℕ => ‖v j‖^2) := by
      simpa [Real.rpow_two] using
        (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mp hv
    have hs : Summable (fun j : ℕ => ‖evenSecondCoefficients v j‖^2) := by
      simpa [Real.rpow_two] using
        (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mp hd
    apply (h2_coefficients_iff_even_frequency v).mpr
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((hm.add hs).mul_left 2)
    intro j
    rw [even_second_coefficient_norm]
    nlinarith [sq_nonneg (‖v j‖ - (2*(j:ℝ))^2*‖v j‖)]

noncomputable def evenSecondSequence (v : ℕ → ℂ) (hv : HasH2Coefficients v) :
    CosineSequenceSpace := ⟨evenSecondCoefficients v, h2_second_coefficients_mem_l2 v hv⟩

end Lemniscate
