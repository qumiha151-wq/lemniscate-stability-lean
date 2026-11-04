import Lemniscate.PeriodicSobolevH2Interpolation
import Lemniscate.PeriodicWeakOperatorEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-! The actual principal operator controls the full H4 norm.
Weak integration by parts gives positivity against the value coordinate;
the existing H2 interpolation estimate then controls the remaining jet.
No finite-mode restriction or new Fourier-weight argument is needed. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

/-- The actual positive principal operator Id + 4 D^4 on complete H4. -/
def circleSobolevPrincipalOperator : CircleSobolevSpace T 4 →L[ℂ] CircleL2 T :=
  circleSobolevCoordinate T 4 0+(4:ℂ) • circleSobolevCoordinate T 4 4

/-- A fixed conservative constant controls the complete derivative-jet norm
by the actual L2 principal operator on every periodic H4 function. -/
theorem circle_sobolev_principal_estimate (f : CircleSobolevSpace T 4) :
    ‖f‖ ≤ 10*‖circleSobolevPrincipalOperator T f‖ := by
  let v := circleSobolevCoordinate T 4 0 f
  let w := circleSobolevCoordinate T 4 4 f
  let a := ‖v‖
  let c := ‖circleSobolevCoordinate T 4 2 f‖
  let d := ‖circleSobolevCoordinate T 4 3 f‖
  let e := ‖w‖
  let A := ‖circleSobolevPrincipalOperator T f‖
  let N := ‖f‖
  let f₂ := circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)
  have ha : 0 ≤ a := norm_nonneg v
  have he : 0 ≤ e := norm_nonneg w
  have hA : 0 ≤ A := norm_nonneg _
  have hN : 0 ≤ N := norm_nonneg f
  have hfourth : inner ℂ v w = inner ℂ
      (circleSobolevCoordinate T 4 2 f) (circleSobolevCoordinate T 4 2 f) :=
    circle_weak_fourth_pairing T _ _ _ _ _
      (circle_sobolev_weak_deriv T 4 f 0) (circle_sobolev_weak_deriv T 4 f 1)
      (circle_sobolev_weak_deriv T 4 f 2) (circle_sobolev_weak_deriv T 4 f 3)
  have hpair : (inner ℂ v (circleSobolevPrincipalOperator T f)).re = a^2+4*c^2 := by
    have hvRe : (inner ℂ v v).re = ‖v‖^2 := by
      simpa only using! (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    have hcRe : (inner ℂ (circleSobolevCoordinate T 4 2 f)
        (circleSobolevCoordinate T 4 2 f)).re = ‖circleSobolevCoordinate T 4 2 f‖^2 := by
      simpa only using!
        (norm_sq_eq_re_inner (𝕜 := ℂ) (circleSobolevCoordinate T 4 2 f)).symm
    change (inner ℂ v (v+(4:ℂ) • w)).re = ‖v‖^2+4*‖circleSobolevCoordinate T 4 2 f‖^2
    rw [inner_add_right,inner_smul_right,hfourth,Complex.add_re,Complex.mul_re]
    simp only [show (4:ℂ).re = (4:ℝ) from rfl,show (4:ℂ).im = (0:ℝ) from rfl,
      zero_mul,sub_zero,hvRe,hcRe]
  have hcauchy : (inner ℂ v (circleSobolevPrincipalOperator T f)).re ≤ a*A :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have haA : a ≤ A := by
    have hs : a^2 ≤ a*A := by nlinarith only [hpair,hcauchy,sq_nonneg c]
    by_cases hz : a = 0
    · simpa only [hz] using hA
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      exact le_of_mul_le_mul_left (by simpa only [pow_two] using hs) hap
  have hvec : (4:ℂ) • w = circleSobolevPrincipalOperator T f-v := by
    change (4:ℂ) • w = (v+(4:ℂ) • w)-v
    abel
  have hfour : 4*e ≤ A+a := by
    calc
      4*e = ‖(4:ℂ) • w‖ := by
        change (4:ℝ)*‖w‖ = ‖(4:ℂ) • w‖
        rw [norm_smul]
        norm_num
      _ = ‖circleSobolevPrincipalOperator T f-v‖ := congrArg norm hvec
      _ ≤ A+a := norm_sub_le _ _
  have heA : e ≤ A := by linarith only [hfour,haA,hA]
  have heA2 : e^2 ≤ A^2 := (sq_le_sq₀ he hA).mpr heA
  have hcoord : c ≤ N := by
    simpa only [c,N,one_mul] using
      (circleSobolevCoordinate T 4 2).le_of_opNorm_le
        (circle_sobolev_coordinate_norm_le T 4 2) f
  have hthird : d^2 ≤ c*e :=
    circle_weak_derivative_norm_sq_product T _ _ _
      (circle_sobolev_weak_deriv T 4 f 2) (circle_sobolev_weak_deriv T 4 f 3)
  have hthird' : d^2 ≤ A*N := by
    have h := hthird.trans (mul_le_mul hcoord heA he hN)
    simpa only [mul_comm N A] using h
  have hlow : ‖f₂‖^2 ≤ 3*A*N :=
    (circle_sobolev_h2_interpolation T f).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left haA (by norm_num : (0:ℝ) ≤ 3)) hN)
  have hsplit : N^2 = ‖f₂‖^2+d^2+e^2 := by
    rw [circle_sobolev_norm_sq T 4 f,circle_sobolev_norm_sq T 2 f₂]
    rw [Fin.sum_univ_castSucc (fun j : Fin 5 => ‖circleSobolevCoordinate T 4 j f‖^2)]
    rw [Fin.sum_univ_castSucc
      (fun j : Fin 4 => ‖circleSobolevCoordinate T 4 j.castSucc f‖^2)]
    rfl
  have hbound : N^2 ≤ 4*A*N+A^2 := by
    rw [hsplit]
    nlinarith only [hlow,hthird',heA2]
  change N ≤ 10*A
  by_contra hn
  have hlt : 10*A < N := lt_of_not_ge hn
  have hprod : 0 < (N-10*A)*(N+6*A) :=
    mul_pos (sub_pos.mpr hlt) (by linarith only [hlt,hA])
  nlinarith only [hprod,hbound,sq_nonneg A]

end Lemniscate
