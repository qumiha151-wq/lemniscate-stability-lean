import LengthGrowth.ActualFlow.TangentStructureEstimate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
namespace LengthGrowth.TangentSpectrum
noncomputable section
open MeasureTheory Real Set

def quarticIncrement (T : ℝ→ℂ) (h : ℝ) := ∫u in 0..1, ‖T (u+h)-T u‖^4

theorem increment_sandwich {T : ℝ→ℂ} (ct : Continuous T) (unit : ∀u, ‖T u‖=1) (h : ℝ) :
    (incrementMoment T h)^2≤quarticIncrement T h ∧ quarticIncrement T h≤4*incrementMoment T h := by
  let g := fun u=>‖T (u+h)-T u‖^2
  have cg : Continuous g := ((ct.comp (continuous_id.add continuous_const)).sub ct).norm.pow 2
  let m := ∫u in (0:ℝ)..1,g u
  have eq : quarticIncrement T h=∫u in 0..1,g u^2 := by
    unfold quarticIncrement;congr 1;funext u;dsimp [g];ring
  rw [eq]
  change m^2≤_ ∧ _≤4*m
  constructor
  · have nn := intervalIntegral.integral_nonneg_of_forall (μ:=volume) (a:=0) (b:=1) (by norm_num) (fun u => sq_nonneg (g u-m))
    have alg (u : ℝ) : (g u-m)^2=g u^2-2*m*g u+m^2 := by ring
    simp_rw [alg] at nn
    rw [intervalIntegral.integral_add (f:=fun u => g u^2-2*m*g u) (g:=fun _ => m^2)
      (((cg.pow 2).sub (continuous_const.mul cg)).intervalIntegrable 0 1) intervalIntegrable_const] at nn
    rw [intervalIntegral.integral_sub (f:=fun u => g u^2) (g:=fun u => 2*m*g u)
      ((cg.pow 2).intervalIntegrable ..) ((continuous_const.mul cg).intervalIntegrable ..),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at nn
    change 0≤_ - 2*m*m + (1-0) • m^2 at nn
    simpa using (show m^2≤∫u in 0..1,g u^2 by simp only [sub_zero,one_smul] at nn; linarith)
  · change _≤4*(∫u in 0..1,g u)
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num) ((cg.pow 2).intervalIntegrable ..)
      ((continuous_const.mul cg).intervalIntegrable ..)
    intro u _
    have b := norm_sub_le (T (u+h)) (T u)
    simp only [unit] at b
    have ub : g u≤4 := (pow_le_pow_left₀ (norm_nonneg _) b 2).trans_eq (by norm_num)
    exact (show g u^2≤4*g u by rw [pow_two];exact mul_le_mul_of_nonneg_right ub (sq_nonneg _))

theorem multiplier_upper (x : ℝ) : ‖Complex.exp (Complex.I*(x:ℂ))-1‖≤|x| := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,Real.norm_eq_abs,abs_mul]
  have b : |Real.sin (x/2)|≤|x/2| := Real.abs_sin_le_abs
  rw [abs_div] at b
  norm_num at b ⊢
  linarith

theorem increment_upper {T : ℝ→ℂ} (ct : Continuous T) (pt : Function.Periodic T 1)
    {U : ℝ} (two : HasSum (fun n=>|omega n|^2*energy T n) (2*U)) (h : ℝ) :
    incrementMoment T h≤h^2*(2*U) := by
  apply hasSum_le _ (increment_parseval ct pt h) (two.mul_left (h^2))
  intro n
  have b := pow_le_pow_left₀ (norm_nonneg _) (multiplier_upper (omega n*h)) 2
  have e := mul_le_mul_of_nonneg_right b (sq_nonneg (‖coeff T n‖))
  change ‖character n h-1‖^2*energy T n≤|omega n*h|^2*energy T n at e
  rwa [sq_abs,mul_pow,mul_comm ((omega n)^2),mul_assoc,←sq_abs (omega n)] at e

end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.increment_upper

