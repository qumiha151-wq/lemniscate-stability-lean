import Lemniscate.PeriodicSobolevDerivatives
import Lemniscate.PeriodicDerivativeGraph
import Mathlib.Algebra.BigOperators.Fin

/-! The H2 interpolation estimate between the value L2 norm and the actual
H4 Sobolev norm. Weak derivative norm products provide the estimate; all
Sobolev norms are the complete derivative square-sum norms.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_sobolev_h2_inclusion_norm_sq (f : CircleSobolevSpace T 4) :
    ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖^2 =
      ‖circleSobolevCoordinate T 4 0 f‖^2+
        ‖circleSobolevCoordinate T 4 1 f‖^2+
        ‖circleSobolevCoordinate T 4 2 f‖^2 := by
  rw [circle_sobolev_norm_sq]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
    circle_sobolev_inclusion_coordinate]
  simp [circle_sobolev_coordinate_apply,add_assoc]

private theorem middle_derivative_norm_product
    (a b c d e : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hb : b^2 ≤ a*c) (hmid : c^2 ≤ b*d) (hd : d^2 ≤ c*e) :
    c^2 ≤ a*e := by
  by_cases hz : c = 0
  · simpa only [hz,zero_pow (by decide : (2:ℕ) ≠ 0)] using mul_nonneg ha he
  · have hfourth : c^4 ≤ b^2*d^2 := by
      calc
        c^4 = (c^2)^2 := by ring
        _ ≤ (b*d)^2 := pow_le_pow_left₀ (sq_nonneg c) hmid 2
        _ = b^2*d^2 := by ring
    have hproduct : b^2*d^2 ≤ (a*e)*c^2 := by
      calc
        b^2*d^2 ≤ (a*c)*(c*e) :=
          mul_le_mul hb hd (sq_nonneg d) (mul_nonneg ha hc)
        _ = (a*e)*c^2 := by ring
    have hcancel : c^2*c^2 ≤ (a*e)*c^2 := by
      calc
        c^2*c^2 = c^4 := by ring
        _ ≤ (a*e)*c^2 := hfourth.trans hproduct
    exact le_of_mul_le_mul_right hcancel (sq_pos_of_ne_zero hz)

theorem circle_sobolev_h2_interpolation (f : CircleSobolevSpace T 4) :
    ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖^2 ≤
      3*‖circleSobolevCoordinate T 4 0 f‖*‖f‖ := by
  let a := ‖circleSobolevCoordinate T 4 0 f‖
  let b := ‖circleSobolevCoordinate T 4 1 f‖
  let c := ‖circleSobolevCoordinate T 4 2 f‖
  let d := ‖circleSobolevCoordinate T 4 3 f‖
  let e := ‖circleSobolevCoordinate T 4 4 f‖
  let N := ‖f‖
  have ha : 0 ≤ a := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have he : 0 ≤ e := norm_nonneg _
  have hb : b^2 ≤ a*c :=
    circle_weak_derivative_norm_sq_product T _ _ _
      (circle_sobolev_weak_deriv T 4 f 0)
      (circle_sobolev_weak_deriv T 4 f 1)
  have hmid : c^2 ≤ b*d :=
    circle_weak_derivative_norm_sq_product T _ _ _
      (circle_sobolev_weak_deriv T 4 f 1)
      (circle_sobolev_weak_deriv T 4 f 2)
  have hd : d^2 ≤ c*e :=
    circle_weak_derivative_norm_sq_product T _ _ _
      (circle_sobolev_weak_deriv T 4 f 2)
      (circle_sobolev_weak_deriv T 4 f 3)
  have hsecond : c^2 ≤ a*e :=
    middle_derivative_norm_product a b c d e ha hc he hb hmid hd
  have hcoord (j : Fin 5) : ‖circleSobolevCoordinate T 4 j f‖ ≤ N := by
    simpa only [N,one_mul] using
      (circleSobolevCoordinate T 4 j).le_of_opNorm_le
        (circle_sobolev_coordinate_norm_le T 4 j) f
  have hfirst : a^2 ≤ a*N := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left (hcoord 0) ha
  have hmiddle : b^2 ≤ a*N :=
    hb.trans (mul_le_mul_of_nonneg_left (hcoord 2) ha)
  have hlast : c^2 ≤ a*N :=
    hsecond.trans (mul_le_mul_of_nonneg_left (hcoord 4) ha)
  calc
    ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖^2 = a^2+b^2+c^2 :=
      circle_sobolev_h2_inclusion_norm_sq T f
    _ ≤ a*N+a*N+a*N := add_le_add (add_le_add hfirst hmiddle) hlast
    _ = 3*‖circleSobolevCoordinate T 4 0 f‖*‖f‖ := by
      dsimp only [a,N]
      ring

end Lemniscate
