import Lemniscate.PeriodicSobolevDerivatives
import Lemniscate.PeriodicDerivativeGraph
import Mathlib.Algebra.BigOperators.Fin

/-! Interpolation in the complete periodic Sobolev scale.
The third weak derivative is estimated by weak integration by parts.
All norms are the derivative square-sum Sobolev norms.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

/-- H3 squared is bounded by twice the product of the H2 and H4 norms. -/
theorem circle_sobolev_h3_interpolation (f : CircleSobolevSpace T 4) :
    ‖circleSobolevInclusion T 3 f‖^2 ≤
      2*‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖*‖f‖ := by
  let g := circleSobolevInclusion T 3 f
  let h := circleSobolevInclusion T 2 g
  change ‖g‖^2 ≤ 2*‖h‖*‖f‖
  have hsplit : ‖g‖^2 = ‖h‖^2+‖circleSobolevCoordinate T 4 3 f‖^2 := by
    rw [circle_sobolev_norm_sq T 3 g,circle_sobolev_norm_sq T 2 h]
    rw [Fin.sum_univ_castSucc
      (fun j : Fin 4 => ‖circleSobolevCoordinate T 3 j g‖^2)]
    rfl
  have hcoord2 : ‖circleSobolevCoordinate T 4 2 f‖ ≤ ‖h‖ := by
    simpa only [h,g,one_mul,circle_sobolev_inclusion_coordinate,
      circle_sobolev_coordinate_apply] using!
      (circleSobolevCoordinate T 2 2).le_of_opNorm_le
        (circle_sobolev_coordinate_norm_le T 2 2) h
  have hcoord4 : ‖circleSobolevCoordinate T 4 4 f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using
      (circleSobolevCoordinate T 4 4).le_of_opNorm_le
        (circle_sobolev_coordinate_norm_le T 4 4) f
  have hmiddle : ‖circleSobolevCoordinate T 4 3 f‖^2 ≤
      ‖circleSobolevCoordinate T 4 2 f‖*‖circleSobolevCoordinate T 4 4 f‖ :=
    circle_weak_derivative_norm_sq_product T _ _ _
      (circle_sobolev_weak_deriv T 4 f 2)
      (circle_sobolev_weak_deriv T 4 f 3)
  have hmiddle' : ‖circleSobolevCoordinate T 4 3 f‖^2 ≤ ‖h‖*‖f‖ :=
    hmiddle.trans (mul_le_mul hcoord2 hcoord4 (norm_nonneg _) (norm_nonneg _))
  have hinclusion2 : ‖h‖ ≤ ‖g‖ := by
    simpa only [h,one_mul] using
      (circleSobolevInclusion T 2).le_of_opNorm_le
        (circle_sobolev_inclusion_norm_le T 2) g
  have hinclusion3 : ‖g‖ ≤ ‖f‖ := by
    simpa only [g,one_mul] using
      (circleSobolevInclusion T 3).le_of_opNorm_le
        (circle_sobolev_inclusion_norm_le T 3) f
  have hlower : ‖h‖^2 ≤ ‖h‖*‖f‖ := by
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_left (hinclusion2.trans hinclusion3) (norm_nonneg h)
  calc
    ‖g‖^2 = ‖h‖^2+‖circleSobolevCoordinate T 4 3 f‖^2 := hsplit
    _ ≤ ‖h‖*‖f‖+‖h‖*‖f‖ := add_le_add hlower hmiddle'
    _ = 2*‖h‖*‖f‖ := by ring

end Lemniscate
