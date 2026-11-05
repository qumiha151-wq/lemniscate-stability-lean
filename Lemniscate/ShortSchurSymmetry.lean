import Lemniscate.ShortSchurMatrices
import Mathlib.Tactic.Abel

namespace Lemniscate
open Matrix

theorem short_outer_self_transpose (v : Fin 15 → ℝ) :
    (shortOuter v v)ᵀ = shortOuter v v := by
  ext i j
  exact mul_comm _ _

theorem short_householder_transpose (h : ℕ → ℝ) :
    (shortHouseholder h)ᵀ = shortHouseholder h := by
  simp only [shortHouseholder, transpose_sub, transpose_one, transpose_smul,
    short_outer_self_transpose]

theorem short_center_projection_transpose :
    shortCenterProjectionᵀ = shortCenterProjection := short_outer_self_transpose _

theorem short_stable_projection_transpose :
    shortStableProjectionᵀ = shortStableProjection := by
  simp only [shortStableProjection, transpose_sub, transpose_one, short_center_projection_transpose]

theorem short_transformed_transpose (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) :
    (shortTransformedCoefficient r h k)ᵀ = shortTransformedCoefficient r h k := by
  by_cases hk : k=0
  · simp only [shortTransformedCoefficient, if_pos hk, transpose_mul,
      short_householder_transpose, short_symmetric_transpose]
    simp only [mul_assoc]
  · by_cases hk4 : k=4
    · simp only [shortTransformedCoefficient, if_neg hk, if_pos hk4,
        transpose_smul, transpose_one]
    · simp only [shortTransformedCoefficient, if_neg hk, if_neg hk4,
        short_symmetric_transpose]

theorem short_g_coefficient_transpose (r : ℝ) (h : ℕ → ℝ) (k : Fin 5) :
    (shortGHeadCoefficient r h k)ᵀ = shortGHeadCoefficient r h k := by
  fin_cases k <;>
    simp only [shortGHeadCoefficient, Matrix.cons_val_zero', Matrix.cons_val_succ',
      transpose_add, transpose_mul,
      transpose_smul, transpose_one, short_stable_projection_transpose,
      short_center_projection_transpose, short_transformed_transpose, mul_assoc] <;> abel

end Lemniscate
