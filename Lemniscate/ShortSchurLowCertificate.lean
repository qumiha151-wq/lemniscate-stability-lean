import Lemniscate.ShortSchurLowData
import Lemniscate.ShortSchurIdentification

/-! The thirty-five checked rational rows bound the actual new low matrix. -/
namespace Lemniscate.CoarseArithmetic
open Matrix Finset

noncomputable def shortCReal : Fin 5 → Matrix (Fin 7) (Fin 7) ℝ :=
  ![shortC0Real,shortC1Real,shortC2Real,shortC3Real,shortC4Real]

theorem short_low_certificate_data_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval (shortLowCertificateData j)) (shortCReal j) := by
  fin_cases j
  · exact short_c0_data_sound
  · exact short_c1_data_sound
  · exact short_c2_data_sound
  · exact short_c3_data_sound
  · exact short_c4_data_sound

theorem short_c_real_identification (j : Fin 5) : shortCReal j =
    shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j := by
  have hj : shortCReal j = shortLowEmbeddingᵀ * shortBReal j * shortLowEmbedding := by
    fin_cases j <;> rfl
  rw [hj, short_bernstein_identification]
  rfl

theorem short_low_row_bound (j : Fin 5) (i : Fin 7) :
    let C := shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j
    C i i + (∑ k : Fin 7, if k=i then 0 else
      |C i k| * ((shortLowWeight j k : ℝ) / (shortLowWeight j i : ℝ))) ≤ -(2/25:ℝ) := by
  let M := integerMatrixInterval (shortLowCertificateData j)
  let C := shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j
  have hM : MatrixContains M C := by
    change MatrixContains M (shortLowBernstein lemniscateFrequencySquared shortActualCoefficient j)
    rw [← short_c_real_identification]
    exact short_low_certificate_data_sound j
  have hrow : C i i + (∑ k : Fin 7, if k=i then 0 else
        |C i k| * ((shortLowWeight j k : ℝ) / (shortLowWeight j i : ℝ))) ≤
      ((M i i).hi : ℝ) + (∑ k : Fin 7, if k=i then 0 else
        (absUpper (M i k) : ℝ) * ((shortLowWeight j k : ℝ) / (shortLowWeight j i : ℝ))) := by
    apply add_le_add (hM i i).2
    apply Finset.sum_le_sum
    intro k _
    by_cases hki : k=i
    · simp only [if_pos hki, le_refl]
    · simp only [if_neg hki]
      apply mul_le_mul_of_nonneg_right (absUpper_sound _ _ (hM i k))
      exact div_nonneg (by exact_mod_cast (short_low_weight_pos j k).le)
        (by exact_mod_cast (short_low_weight_pos j i).le)
  have hcast : ((M i i).hi : ℝ) + (∑ k : Fin 7, if k=i then 0 else
        (absUpper (M i k) : ℝ) * ((shortLowWeight j k : ℝ) / (shortLowWeight j i : ℝ))) =
      (shortLowRowUpper j i : ℝ) := by
    unfold shortLowRowUpper
    simp only [Rat.cast_add, Rat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    by_cases hki : k=i
    · simp only [if_pos hki, Rat.cast_zero]
    · simp only [if_neg hki, Rat.cast_mul, Rat.cast_div]
      rfl
  have hnum : (shortLowRowUpper j i : ℝ) < -(2/25:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (short_thirty_five_rows j i)
    simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using h
  exact (hrow.trans_eq hcast).trans hnum.le

end Lemniscate.CoarseArithmetic
