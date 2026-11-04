import Lemniscate.PeriodicSobolevSpace
import Lemniscate.PeriodicDerivativeGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-! The combined stability energy controls the actual H2 Sobolev norm.

Weak integration by parts controls the first derivative between the value
and the second derivative.  The additional bounded L2 metric can therefore
be included without changing the lower control of the H2 norm.
-/

noncomputable section
namespace Lemniscate
open Complex MeasureTheory

private theorem energy_norm_real
    (a b c d m N κ : ℝ) (hκ : 0 ≤ κ)
    (hN : N = a^2+b^2+c^2) (hweak : b^2 ≤ a*c) (hV : d^2 ≤ m^2*N) :
    N ≤ 2*(a^2+4*c^2+κ*d^2) ∧
      a^2+4*c^2+κ*d^2 ≤ (4+κ*m^2)*N := by
  have hlow : N ≤ 2*(a^2+4*c^2) := by
    nlinarith only [hN,hweak,sq_nonneg (a-c),sq_nonneg a,sq_nonneg c]
  have hupp : a^2+4*c^2 ≤ 4*N := by
    nlinarith only [hN,sq_nonneg a,sq_nonneg b]
  refine ⟨hlow.trans ?_,?_⟩
  · exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (mul_nonneg hκ (sq_nonneg d))) (by norm_num)
  · calc
      a^2+4*c^2+κ*d^2 ≤ 4*N+κ*(m^2*N) :=
        add_le_add hupp (mul_le_mul_of_nonneg_left hV hκ)
      _ = (4+κ*m^2)*N := by ring

variable (T : ℝ) [Fact (0 < T)]

/-- The actual H2 norm and the combined principal-plus-metric energy are
equivalent. Setting kappa to zero also gives the principal energy comparison. -/
theorem circle_sobolev_energy_norm_equivalence
    (V : CircleL2 T →L[ℂ] CircleL2 T) (κ : ℝ) (hκ : 0 ≤ κ)
    (f : CircleSobolevSpace T 2) :
    let E := ‖circleSobolevCoordinate T 2 0 f‖^2+
      4*‖circleSobolevCoordinate T 2 2 f‖^2+
      κ*‖V (circleSobolevCoordinate T 2 0 f)‖^2
    ‖f‖^2 ≤ 2*E ∧ E ≤ (4+κ*‖V‖^2)*‖f‖^2 := by
  let a := ‖circleSobolevCoordinate T 2 0 f‖
  let b := ‖circleSobolevCoordinate T 2 1 f‖
  let c := ‖circleSobolevCoordinate T 2 2 f‖
  let d := ‖V (circleSobolevCoordinate T 2 0 f)‖
  have hN : ‖f‖^2 = a^2+b^2+c^2 := by
    dsimp only [a,b,c]
    rw [circle_sobolev_norm_sq]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    simp [circle_sobolev_coordinate_apply,add_assoc]
  have hweak : b^2 ≤ a*c := by
    simpa only [a,b,c,circle_sobolev_coordinate_apply] using!
      (circle_weak_derivative_norm_sq_product T _ _ _
        (circle_sobolev_weak_deriv T 2 f 0) (circle_sobolev_weak_deriv T 2 f 1))
  have hvalue : ‖circleSobolevCoordinate T 2 0 f‖ ≤ ‖f‖ := by
    simpa only [one_mul] using
      (circleSobolevCoordinate T 2 0).le_of_opNorm_le
        (circle_sobolev_coordinate_norm_le T 2 0) f
  have hVnorm : d ≤ ‖V‖*‖f‖ :=
    (V.le_opNorm _).trans (mul_le_mul_of_nonneg_left hvalue (norm_nonneg V))
  have hV : d^2 ≤ ‖V‖^2*‖f‖^2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (norm_nonneg V) (norm_nonneg f))).mpr hVnorm
    simpa only [mul_pow] using hs
  exact energy_norm_real a b c d ‖V‖ (‖f‖^2) κ hκ hN hweak hV

end Lemniscate
