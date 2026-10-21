import Lemniscate.CosineSecondCoefficients

/-! Second derivative multipliers for positive even sine frequencies. The
offset is 1 for the full family and 2 after removing its first mode. -/
namespace Lemniscate
open CoarseArithmetic
open scoped ENNReal

noncomputable def sineSecondCoefficients (offset : ℕ) (v : ℕ → ℂ) (j : ℕ) : ℂ :=
  ((-(2*((j:ℝ)+(offset:ℝ)))^2 : ℝ):ℂ)*v j

theorem sine_second_coefficient_norm (offset : ℕ) (v : ℕ → ℂ) (j : ℕ) :
    ‖sineSecondCoefficients offset v j‖ = (2*((j:ℝ)+(offset:ℝ)))^2*‖v j‖ := by
  simp only [sineSecondCoefficients, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, abs_of_nonneg (sq_nonneg (2*((j:ℝ)+(offset:ℝ))))]

theorem h2_sine_second_coefficients_mem_l2 (offset : ℕ) (v : ℕ → ℂ)
    (hv : HasH2Coefficients v) : Memℓp (sineSecondCoefficients offset v) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, sine_second_coefficient_norm]
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _
    (hv.mul_left ((8*(1+(offset:ℝ)^2))^2))
  intro j
  have hw : (2*((j:ℝ)+(offset:ℝ)))^2 ≤
      (8*(1+(offset:ℝ)^2))*frequencyWeight j := by
    unfold frequencyWeight
    nlinarith [sq_nonneg ((j:ℝ)-(offset:ℝ)),
      mul_nonneg (sq_nonneg (j:ℝ)) (sq_nonneg (offset:ℝ))]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ (2*((j:ℝ)+(offset:ℝ)))^2*‖v j‖)
    (mul_le_mul_of_nonneg_right hw (norm_nonneg (v j))) 2
  convert! hs using 1
  ring

theorem h2_iff_sine_second_l2 (offset : ℕ) (hoff : 0 < offset) (v : ℕ → ℂ) :
    HasH2Coefficients v ↔ Memℓp (sineSecondCoefficients offset v) 2 := by
  constructor
  · exact h2_sine_second_coefficients_mem_l2 offset v
  · intro hd
    have hs : Summable (fun j : ℕ => ‖sineSecondCoefficients offset v j‖^2) := by
      simpa [Real.rpow_two] using
        (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mp hd
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
    intro j
    rw [sine_second_coefficient_norm]
    have ho : (1:ℝ) ≤ (offset:ℝ) := by exact_mod_cast hoff
    have hw : frequencyWeight j ≤ (2*((j:ℝ)+(offset:ℝ)))^2 := by
      unfold frequencyWeight
      nlinarith [Nat.cast_nonneg (α := ℝ) j,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (Nat.cast_nonneg (α := ℝ) offset)]
    exact pow_le_pow_left₀ (mul_nonneg (frequencyWeight_pos j).le (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hw (norm_nonneg _)) 2

noncomputable def sineSecondSequence (offset : ℕ) (v : ℕ → ℂ)
    (hv : HasH2Coefficients v) : CosineSequenceSpace :=
  ⟨sineSecondCoefficients offset v, h2_sine_second_coefficients_mem_l2 offset v hv⟩

end Lemniscate
