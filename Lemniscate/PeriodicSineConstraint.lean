import Lemniscate.PeriodicSineTail
import Lemniscate.SineConstrainedForm

/-! Realize the coefficient constraint as actual L2 orthogonality. The vector
is specified by the proved nome/theta coefficient series. Its identification
with the geometric rotation vector, and the differential energy identity,
remain separate obligations. -/
namespace Lemniscate
open Complex CoarseArithmetic

variable (T : ℝ) [Fact (0 < T)]

noncomputable def circleSineConstraintVector : CircleL2 T :=
  circleSineBlockFunction T 1 sineTailVector

theorem circle_sine_constraint_inner (u : ℂ) (v : SineTailSpace) :
    inner ℂ (circleSineConstraintVector T) (circleSineBlockFunction T u v) =
      u+inner ℂ sineTailVector v := by
  simp only [circleSineConstraintVector, circle_sine_block_inner, map_one, one_mul]

theorem circle_sine_constraint_orthogonal_iff (u : ℂ) (v : SineTailSpace) :
    inner ℂ (circleSineConstraintVector T) (circleSineBlockFunction T u v) = 0 ↔
      u+inner ℂ sineTailVector v = 0 := by
  rw [circle_sine_constraint_inner]

theorem circle_sine_constraint_vector_ne_zero : circleSineConstraintVector T ≠ 0 := by
  intro h
  have hn := circle_sine_block_norm_sq T (1:ℂ) sineTailVector
  change ‖circleSineConstraintVector T‖^2 = _ at hn
  rw [h, norm_zero, zero_pow (by decide), norm_one, one_pow] at hn
  nlinarith [sq_nonneg ‖sineTailVector‖]

theorem circle_sine_constrained_coefficient_energy (u : ℂ) (v : SineTailSpace)
    (hv : HasSineTailH2Coefficients v)
    (horth : inner ℂ (circleSineConstraintVector T) (circleSineBlockFunction T u v) = 0) :
    sineH2BlockForm u v ≤ -75*‖circleSineBlockFunction T u v‖^2 := by
  rw [circle_sine_block_norm_sq]
  exact sine_h2_constrained_dissipative u v hv
    ((circle_sine_constraint_orthogonal_iff T u v).mp horth)

end Lemniscate
