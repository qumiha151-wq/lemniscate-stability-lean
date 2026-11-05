import Lemniscate.ShortSchurLowData

/-! Small ℓ¹ bounds for the actual finite transformations.  Coarse bounds
on the projections suffice; exact square-root cancellation is unnecessary. -/
namespace Lemniscate.CoarseArithmetic
open Matrix Finset

def shortTransformData : Fin 5 → Matrix (Fin 15) (Fin 15) IntegerInterval :=
  ![shortUData,shortStageUTData,shortStageTiUData,shortPData,shortP0Data]

noncomputable def shortTransformReal : Fin 5 → Matrix (Fin 15) (Fin 15) ℝ :=
  ![shortHouseholder shortActualCoefficient,shortStageUTReal,shortStageTiUReal,
    shortStableProjection,shortCenterProjection]

def shortTransformL1Bound (j : Fin 5) : ℚ := if j.val<3 then 100 else 2

def shortTransformRowSumUpper (j : Fin 5) (i : Fin 15) : ℚ :=
  ∑ k : Fin 15, absUpper ((shortTransformData j i k).toInterval)

def shortTransformColSumUpper (j : Fin 5) (i : Fin 15) : ℚ :=
  ∑ k : Fin 15, absUpper ((shortTransformData j k i).toInterval)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_transform_l1_arithmetic : ∀ j i,
    shortTransformRowSumUpper j i < shortTransformL1Bound j ∧
    shortTransformColSumUpper j i < shortTransformL1Bound j := by decide +kernel

theorem short_transform_data_sound (j : Fin 5) :
    MatrixContains (integerMatrixInterval (shortTransformData j)) (shortTransformReal j) := by
  fin_cases j
  · exact short_u_data_sound
  · exact short_stage_ut_sound
  · exact short_stage_tiu_sound
  · exact short_p_data_sound
  · exact short_p0_data_sound

theorem short_transform_l1_bound (j : Fin 5) (i : Fin 15) :
    (∑ k : Fin 15, |shortTransformReal j i k|) ≤ (shortTransformL1Bound j : ℝ) ∧
    (∑ k : Fin 15, |shortTransformReal j k i|) ≤ (shortTransformL1Bound j : ℝ) := by
  have hd := short_transform_data_sound j
  have hrow : (∑ k : Fin 15, |shortTransformReal j i k|) ≤
      (shortTransformRowSumUpper j i : ℝ) := by
    rw [shortTransformRowSumUpper, Rat.cast_sum]
    exact Finset.sum_le_sum (fun k _ => absUpper_sound _ _ (hd i k))
  have hcol : (∑ k : Fin 15, |shortTransformReal j k i|) ≤
      (shortTransformColSumUpper j i : ℝ) := by
    rw [shortTransformColSumUpper, Rat.cast_sum]
    exact Finset.sum_le_sum (fun k _ => absUpper_sound _ _ (hd k i))
  exact ⟨hrow.trans ((Rat.cast_le (K := ℝ)).mpr (short_transform_l1_arithmetic j i).1.le),
    hcol.trans ((Rat.cast_le (K := ℝ)).mpr (short_transform_l1_arithmetic j i).2.le)⟩

def shortFColumnSumUpper (k : Fin 7) : ℚ :=
  ∑ i : Fin 15, absUpper ((shortFData i k).toInterval)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem short_f_column_arithmetic : ∀ k, shortFColumnSumUpper k < 2 := by decide +kernel

theorem short_f_column_l1_bound (k : Fin 7) : (∑ i : Fin 15, |shortLowEmbedding i k|) ≤ 2 := by
  have hf : (∑ i : Fin 15, |shortLowEmbedding i k|) ≤ (shortFColumnSumUpper k : ℝ) := by
    rw [shortFColumnSumUpper, Rat.cast_sum]
    exact Finset.sum_le_sum (fun i _ => absUpper_sound _ _ (short_f_data_sound i k))
  exact hf.trans (by exact_mod_cast (short_f_column_arithmetic k).le)

end Lemniscate.CoarseArithmetic
