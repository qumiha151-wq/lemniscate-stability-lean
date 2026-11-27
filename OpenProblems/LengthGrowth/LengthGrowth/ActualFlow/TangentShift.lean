import LengthGrowth.ActualFlow.TangentFourierMoment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
open MeasureTheory Real
namespace LengthGrowth.TangentSpectrum
noncomputable section

def character (n : ℤ) (x : ℝ) : ℂ := Complex.exp (Complex.I*((omega n*x:ℝ):ℂ))
theorem character_add (n : ℤ) (x h : ℝ) :
    character n (x+h)=character n x*character n h := by
  unfold character
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring
theorem character_periodic (n : ℤ) : Function.Periodic (character n) 1 := by
  intro x
  rw [character_add]
  have one : character n 1=1 := by
    unfold character omega
    convert Complex.exp_int_mul_two_pi_mul_I n using 2; push_cast; ring
  rw [one,mul_one]
theorem coeff_formula (f : ℝ→ℂ) (n : ℤ) :
    coeff f n=∫x in 0..1,character (-n) x*f x := by
  rw [coeff,fourierCoeffOn_eq_integral]
  norm_num only [sub_zero,div_one,one_smul]
  apply intervalIntegral.integral_congr
  intro x _
  simp only [smul_eq_mul,fourier_coe_apply]
  change Complex.exp _ * f x=Complex.exp _*f x
  congr 2
  unfold omega
  push_cast
  ring

theorem coeff_shift_diff {f : ℝ→ℂ} (cf : Continuous f) (pf : Function.Periodic f 1)
    (h : ℝ) (n : ℤ) :
    coeff (fun u=>f (u+h)-f u) n=(character n h-1)*coeff f n := by
  let g := fun x => character (-n) x*f x
  have per : Function.Periodic g 1 := (character_periodic (-n)).mul pf
  have rel (x : ℝ) : character n h*g (x+h)=character (-n) x*f (x+h) := by
    dsimp only [g]
    rw [character_add]
    have canc : character n h*character (-n) h=1 := by
      unfold character omega
      rw [←Complex.exp_add]
      convert Complex.exp_zero using 2
      push_cast
      ring
    linear_combination character (-n) x*f (x+h)*canc
  have cc : Continuous (character (-n)) := by unfold character;fun_prop
  rw [coeff_formula,coeff_formula,sub_one_mul]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (f:=fun x=>character (-n) x*f (x+h)) (g:=fun x=>character (-n) x*f x) ((cc.mul (cf.comp (continuous_id.add continuous_const))).intervalIntegrable _ _)
    ((cc.mul cf).intervalIntegrable _ _)]
  congr 1
  simp_rw [←rel,intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_add_right]
  have eq := per.intervalIntegral_add_eq h 0
  simpa [g,add_comm] using congrArg (fun v => character n h*v) eq

def incrementMoment (f : ℝ→ℂ) (h : ℝ) := ∫u in 0..1, ‖f (u+h)-f u‖^2

theorem increment_parseval {f : ℝ→ℂ} (cf : Continuous f) (pf : Function.Periodic f 1) (h : ℝ) :
    HasSum (fun n=>‖character n h-1‖^2*energy f n) (incrementMoment f h) := by
  have hp := parseval (fun u=>f (u+h)-f u) ((cf.comp (continuous_id.add continuous_const)).sub cf)
  change HasSum (fun n => ‖coeff (fun u=>f (u+h)-f u) n‖^2) _ at hp
  simpa only [energy,coeff_shift_diff cf pf,norm_mul,mul_pow,incrementMoment] using hp

end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.increment_parseval

