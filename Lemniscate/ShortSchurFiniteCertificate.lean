import Lemniscate.ShortSchurHighIdentification

/-! The finite high and coupling certificates enclose the same full kernel
whose external columns retain all genuine Fourier coefficients. -/
namespace Lemniscate.CoarseArithmetic
open Matrix Finset

noncomputable def shortCrossInsideReal : Fin 5 → Matrix (Fin 7) (Fin 15) ℝ :=
  ![shortM0Real,shortM1Real,shortM2Real,shortM3Real,shortM4Real]

noncomputable def shortCrossOutsideReal : Fin 5 → Matrix (Fin 7) (Fin 14) ℝ :=
  ![shortHighCrossOut0Real,shortHighCrossOut1Real,shortHighCrossOut2Real,
    shortHighCrossOut3Real,shortHighCrossOut4Real]

noncomputable def shortSelectedCrossReal (j : Fin 5) (i : Fin 7) (k : Fin 22) : ℝ :=
  match shortHighLookup k with
  | .inl a => shortCrossInsideReal j i a
  | .inr a => shortCrossOutsideReal j i a

private theorem short_head_data_family_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval
      (![shortB0Data,shortB1Data,shortB2Data,shortB3Data,shortB4Data] j)) (shortBReal j) := by
  fin_cases j
  · exact short_b0_data_sound
  · exact short_b1_data_sound
  · exact short_b2_data_sound
  · exact short_b3_data_sound
  · exact short_b4_data_sound

private theorem short_exterior_data_family_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval (shortExteriorBData j)) (shortExteriorBReal j) := by
  fin_cases j
  · exact short_exterior_b0_sound
  · exact short_exterior_b1_sound
  · exact short_exterior_b2_sound
  · exact short_exterior_b3_sound
  · exact short_exterior_b4_sound

private theorem short_raw_data_family_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval (shortRawHighData j)) (shortRawHighReal j) := by
  fin_cases j
  · exact short_high_raw0_sound
  · exact short_high_raw1_sound
  · exact short_high_raw2_sound
  · exact short_high_raw3_sound
  · exact short_high_raw4_sound

theorem short_selected_high_data_sound (j : Fin 5) (i k : Fin 22) :
    Contains (shortSelectedHighData j i k).toInterval (shortSelectedHighReal j i k) := by
  unfold shortSelectedHighData shortSelectedHighReal
  cases shortHighLookup i <;> cases shortHighLookup k
  · exact short_head_data_family_sound j _ _
  · exact short_exterior_data_family_sound j _ _
  · exact short_exterior_data_family_sound j _ _
  · exact short_raw_data_family_sound j _ _

private theorem short_cross_inside_data_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval (shortCrossInsideData j)) (shortCrossInsideReal j) := by
  fin_cases j
  · exact short_m0_data_sound
  · exact short_m1_data_sound
  · exact short_m2_data_sound
  · exact short_m3_data_sound
  · exact short_m4_data_sound

private theorem short_cross_outside_data_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval (shortCrossOutsideData j)) (shortCrossOutsideReal j) := by
  fin_cases j
  · exact short_high_crossout0_sound
  · exact short_high_crossout1_sound
  · exact short_high_crossout2_sound
  · exact short_high_crossout3_sound
  · exact short_high_crossout4_sound

theorem short_selected_cross_data_sound (j : Fin 5) (i : Fin 7) (k : Fin 22) :
    Contains (shortSelectedCrossData j i k).toInterval (shortSelectedCrossReal j i k) := by
  unfold shortSelectedCrossData shortSelectedCrossReal
  cases shortHighLookup k
  · exact short_cross_inside_data_sound j _ _
  · exact short_cross_outside_data_sound j _ _

theorem short_head_index_half (a : Fin 15) :
    shortHeadIndex ((a.val:ℤ)-7) = some a := by
  unfold shortHeadIndex
  rw [dif_pos (by constructor <;> omega)]
  congr 1
  apply Fin.ext
  change ((a.val:ℤ)-7+7).toNat = a.val
  simp only [sub_add_cancel, Int.toNat_natCast]

noncomputable def shortCrossEntry (j : Fin 5) (i : Fin 7) (n : ℤ) : ℝ :=
  (∑ a : Fin 15, shortLowEmbedding a i *
    shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j ((a.val:ℤ)-7) n) /
      (2*(n:ℝ))^2

noncomputable def shortHighEntry (j : Fin 5) (n m : ℤ) : ℝ :=
  shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j n m /
    ((2*(n:ℝ))^2*(2*(m:ℝ))^2)

private theorem short_cross_inside_entry (j : Fin 5) (i : Fin 7) (a : Fin 15) :
    shortCrossInsideReal j i a = ∑ b : Fin 15, shortLowEmbedding b i *
      shortBernsteinHead lemniscateFrequencySquared shortActualCoefficient j b a := by
  have hh : shortCrossInsideReal j = shortLowEmbeddingᵀ * shortBReal j := by fin_cases j <;> rfl
  rw [hh, short_bernstein_identification]
  rfl

private theorem short_cross_outside_entry (j : Fin 5) (i : Fin 7) (a : Fin 14) :
    shortCrossOutsideReal j i a = ∑ b : Fin 15, shortLowEmbedding b i *
      shortOutsideBernsteinColumn lemniscateFrequencySquared shortActualCoefficient j
        (shortOutsideHalfFrequency a) b := by
  have hh : shortCrossOutsideReal j = shortLowEmbeddingᵀ * shortExteriorBReal j := by fin_cases j <;> rfl
  rw [hh]
  simp only [Matrix.mul_apply, transpose_apply, short_exterior_b_identification]

theorem short_selected_cross_identification (j : Fin 5) (i : Fin 7) (k : Fin 22) :
    shortSelectedCrossReal j i k = ∑ a : Fin 15, shortLowEmbedding a i *
      shortBernsteinKernel lemniscateFrequencySquared shortActualCoefficient j
        ((a.val:ℤ)-7) (shortHighHalfFrequency k) := by
  have hk := short_high_lookup_spec k
  unfold shortSelectedCrossReal
  cases hlk : shortHighLookup k
  all_goals simp only [hlk] at hk
  all_goals dsimp only
  · rw [short_cross_inside_entry]
    apply Finset.sum_congr rfl
    intro a _
    rw [shortBernsteinKernel, short_head_index_half, hk]
  · rw [short_cross_outside_entry]
    apply Finset.sum_congr rfl
    intro a _
    rw [shortBernsteinKernel, short_head_index_half, hk.1, hk.2]

theorem short_high_scale_cast (i : Fin 22) :
    (shortHighScale i : ℝ) = 1/(2*(shortHighHalfFrequency i:ℝ))^2 := by
  unfold shortHighScale
  push_cast
  rfl

theorem short_finite_high_entry_sound (j : Fin 5) (i k : Fin 22) :
    Contains (shortEData j i k).toInterval
      (shortHighEntry j (shortHighHalfFrequency i) (shortHighHalfFrequency k)) := by
  have hcomp := integer_mul_sound _ _ _ _ (integer_point_sound (shortHighScale i*shortHighScale k))
    (short_selected_high_data_sound j i k)
  have hcmp : IntegerEncloses (shortEData j i k)
      (integerMul (integerPoint (shortHighScale i*shortHighScale k)) (shortSelectedHighData j i k)) := by
    fin_cases j
    · exact short_e0_comparison i k
    · exact short_e1_comparison i k
    · exact short_e2_comparison i k
    · exact short_e3_comparison i k
    · exact short_e4_comparison i k
  have hle := integer_encloses_sound _ _ hcmp
  have h := hcomp.mono hle.1 hle.2
  have heq : ((shortHighScale i*shortHighScale k:ℚ):ℝ)*shortSelectedHighReal j i k =
      shortHighEntry j (shortHighHalfFrequency i) (shortHighHalfFrequency k) := by
    rw [Rat.cast_mul, short_high_scale_cast, short_high_scale_cast,
      short_selected_high_identification]
    simp only [shortHighEntry, div_eq_mul_inv, one_mul, _root_.mul_inv_rev]
    ring
  rw [heq] at h
  exact h

theorem short_finite_cross_entry_sound (j : Fin 5) (i : Fin 7) (k : Fin 22) :
    Contains (shortDData j i k).toInterval (shortCrossEntry j i (shortHighHalfFrequency k)) := by
  have hcomp := integer_mul_sound _ _ _ _ (integer_point_sound (shortHighScale k))
    (short_selected_cross_data_sound j i k)
  have hcmp : IntegerEncloses (shortDData j i k)
      (integerMul (integerPoint (shortHighScale k)) (shortSelectedCrossData j i k)) := by
    fin_cases j
    · exact short_d0_comparison i k
    · exact short_d1_comparison i k
    · exact short_d2_comparison i k
    · exact short_d3_comparison i k
    · exact short_d4_comparison i k
  have hle := integer_encloses_sound _ _ hcmp
  have h := hcomp.mono hle.1 hle.2
  have heq : (shortHighScale k:ℝ)*shortSelectedCrossReal j i k =
      shortCrossEntry j i (shortHighHalfFrequency k) := by
    rw [short_high_scale_cast, short_selected_cross_identification]
    simp only [shortCrossEntry, div_eq_mul_inv, one_mul]
    ring
  rw [heq] at h
  exact h

end Lemniscate.CoarseArithmetic
