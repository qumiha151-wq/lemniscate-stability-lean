import Lemniscate.ShortSchurStages
import Mathlib.Tactic.Module

/-! Stored interval computations are identified with the actual, freshly
defined seven-mode G polynomial. No row estimate is assumed in this file. -/
namespace Lemniscate.CoarseArithmetic
open Matrix

theorem short_stage_h0_identification : shortStageH0Real =
    shortTransformedCoefficient lemniscateFrequencySquared shortActualCoefficient 0 := rfl
theorem short_stage_h1_identification : shortStageH1Real =
    shortTransformedCoefficient lemniscateFrequencySquared shortActualCoefficient 1 := rfl
theorem short_stage_h2_identification : shortStageH2Real =
    shortTransformedCoefficient lemniscateFrequencySquared shortActualCoefficient 2 := rfl
theorem short_stage_h3_identification : shortStageH3Real =
    shortTransformedCoefficient lemniscateFrequencySquared shortActualCoefficient 3 := rfl

private theorem short_cross_transpose (k : Fin 5) :
    (shortCenterProjection * shortTransformedCoefficient lemniscateFrequencySquared
      shortActualCoefficient k * shortStableProjection)ᵀ =
    shortStableProjection * shortTransformedCoefficient lemniscateFrequencySquared
      shortActualCoefficient k * shortCenterProjection := by
  simp only [transpose_mul, short_stable_projection_transpose,
    short_center_projection_transpose, short_transformed_transpose, mul_assoc]

theorem short_stage_g0_identification : shortStageG0Real =
    shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient 0 := by
  change shortStableProjection * shortTransformedCoefficient _ _ 0 * shortStableProjection +
    shortCenterProjection * shortTransformedCoefficient _ _ 1 * shortStableProjection +
    (shortCenterProjection * shortTransformedCoefficient _ _ 1 * shortStableProjection)ᵀ +
    shortCenterProjection * shortTransformedCoefficient _ _ 2 * shortCenterProjection +
    (1/2:ℝ) • (1 : Matrix (Fin 15) (Fin 15) ℝ) = _
  rw [short_cross_transpose]
  rfl

theorem short_stage_g1_identification : shortStageG1Real =
    shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient 1 := by
  change shortStableProjection * shortTransformedCoefficient _ _ 1 * shortStableProjection +
    shortCenterProjection * shortTransformedCoefficient _ _ 2 * shortStableProjection +
    (shortCenterProjection * shortTransformedCoefficient _ _ 2 * shortStableProjection)ᵀ = _
  rw [short_cross_transpose]
  rfl

theorem short_stage_g2_identification : shortStageG2Real =
    shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient 2 := by
  change shortStableProjection * shortTransformedCoefficient _ _ 2 * shortStableProjection +
    shortCenterProjection * shortTransformedCoefficient _ _ 3 * shortStableProjection +
    (shortCenterProjection * shortTransformedCoefficient _ _ 3 * shortStableProjection)ᵀ +
    (-4*lemniscateFrequencySquared^2) • shortCenterProjection = _
  rw [short_cross_transpose]
  rfl

theorem short_stage_g3_identification : shortStagePH3PReal =
    shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient 3 := rfl

theorem short_stage_g4_identification : shortStageG4Real =
    shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient 4 := rfl

noncomputable def shortStageGVector : Fin 5 → Matrix (Fin 15) (Fin 15) ℝ :=
  ![shortStageG0Real,shortStageG1Real,shortStageG2Real,shortStagePH3PReal,shortStageG4Real]

theorem short_stage_g_identification (k : Fin 5) : shortStageGVector k =
    shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient k := by
  fin_cases k
  · exact short_stage_g0_identification
  · exact short_stage_g1_identification
  · exact short_stage_g2_identification
  · exact short_stage_g3_identification
  · exact short_stage_g4_identification

noncomputable def shortBReal : Fin 5 → Matrix (Fin 15) (Fin 15) ℝ :=
  ![shortB0Real,shortB1Real,shortB2Real,shortB3Real,shortB4Real]

theorem short_bernstein_identification (j : Fin 5) : shortBReal j =
    shortBernsteinHead lemniscateFrequencySquared shortActualCoefficient j := by
  have hG : shortStageGVector = shortGHeadCoefficient lemniscateFrequencySquared shortActualCoefficient :=
    funext short_stage_g_identification
  rw [shortBernsteinHead, ← hG]
  fin_cases j <;>
    norm_num [shortBReal, shortB0Real, shortB1Real, shortB2Real, shortB3Real, shortB4Real,
      shortStageGVector, shortBernsteinWeight, Fin.sum_univ_succ, Nat.choose,
      shortStageB0term0Real,
      shortStageB1term0Real,shortStageB1term1Real,shortStageB1sum1Real,
      shortStageB2term0Real,shortStageB2term1Real,shortStageB2term2Real,
      shortStageB2sum1Real,shortStageB2sum2Real,
      shortStageB3term0Real,shortStageB3term1Real,shortStageB3term2Real,shortStageB3term3Real,
      shortStageB3sum1Real,shortStageB3sum2Real,shortStageB3sum3Real,
      shortStageB4term0Real,shortStageB4term1Real,shortStageB4term2Real,shortStageB4term3Real,shortStageB4term4Real,
      shortStageB4sum1Real,shortStageB4sum2Real,shortStageB4sum3Real,shortStageB4sum4Real] <;> module

end Lemniscate.CoarseArithmetic
