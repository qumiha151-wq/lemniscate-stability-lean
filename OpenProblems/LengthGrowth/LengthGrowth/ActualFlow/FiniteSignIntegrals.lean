import LengthGrowth.IntervalL2
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Positivity

/-! Integral estimates for one period and its subintervals. -/
noncomputable section
open MeasureTheory Function
namespace LengthGrowth.ActualFlow.FiniteSignIntegrals

theorem cubic_lower {k : ℝ → ℝ} (hk : Continuous k) :
    (∫ x in (0:ℝ)..1, k x^2)*Real.sqrt (∫ x in (0:ℝ)..1, k x^2)
      ≤ ∫ x in (0:ℝ)..1, |k x|^3 := by
  let B := ∫ x in (0:ℝ)..1, k x^2
  let q := Real.sqrt B
  have hB : 0 ≤ B := intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2=B := Real.sq_sqrt hB
  have pt (x : ℝ) : (3*q/2)*k x^2 ≤ |k x|^3+q^3/2 := by
    have h := mul_nonneg (sq_nonneg (|k x|-q)) (add_nonneg (abs_nonneg (k x)) (div_nonneg hq (by norm_num : (0:ℝ)≤2)))
    nlinarith [show q*|k x|^2=q*k x^2 by rw [sq_abs]]
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (((hk.pow 2).const_mul (3*q/2)).intervalIntegrable 0 1)
    (((hk.abs.pow 3).add continuous_const).intervalIntegrable 0 1) (fun x _ => pt x)
  change (∫ x in (0:ℝ)..1, (3*q/2)*k x^2) ≤ ∫ x in (0:ℝ)..1, |k x|^3+q^3/2 at hi
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun x => |k x|^3) (g := fun _ => q^3/2)
      ((hk.abs.pow 3).intervalIntegrable 0 1) intervalIntegrable_const] at hi
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at hi
  change 3*q/2*B ≤ _ at hi
  change B*q ≤ _
  nlinarith [congrArg (fun t : ℝ => t*q) hq2]

theorem integral_abs_unit {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in (0:ℝ)..1, |F x|) ≤ Real.sqrt (∫ x in (0:ℝ)..1, F x^2) := by
  have h := LengthGrowth.interval_integral_abs_mul_le (f := fun _ : ℝ => (1:ℝ))
    continuous_const hF (by norm_num : (0:ℝ) ≤ 1)
  simpa using h

theorem periodic_window {F : ℝ → ℝ} (hF : Continuous F) (hp : Periodic F 1)
    (c z : ℝ) {l : ℝ} (hl : 0≤l) (hl1 : l≤1) :
    (∫ x in z..z+l, |F x|) ≤ c*l + Real.sqrt (l * ∫ x in (0:ℝ)..1, (|F x|-c)^2) := by
  let g := fun x => |F x|-c
  have hg : Continuous g := hF.abs.sub continuous_const
  have hgperiod : Periodic (fun x => g x^2) 1 := by
    intro x
    simp only [g,hp x]
  have hab : z ≤ z+l := by linarith
  have hsub := intervalIntegral.integral_mono_interval (μ := volume) (le_refl z) hab
    (by linarith : z+l ≤ z+1) (Filter.Eventually.of_forall (fun x => sq_nonneg (g x)))
    ((hg.pow 2).intervalIntegrable z (z+1))
  rw [hgperiod.intervalIntegral_add_eq z 0,zero_add] at hsub
  have hcs := LengthGrowth.interval_integral_mul_sq_le (f := fun _ : ℝ => (1:ℝ))
    continuous_const hg hab
  simp only [one_mul,one_pow,intervalIntegral.integral_const,smul_eq_mul,mul_one,add_sub_cancel_left] at hcs
  have hsq := hcs.trans (mul_le_mul_of_nonneg_left hsub hl)
  have hR : 0 ≤ ∫ x in (0:ℝ)..1, g x^2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun x => sq_nonneg _)
  have hbound : (∫ x in z..z+l, g x) ≤ Real.sqrt (l*∫ x in (0:ℝ)..1, g x^2) := by
    nlinarith [Real.sq_sqrt (mul_nonneg hl hR),Real.sqrt_nonneg (l*∫ x in (0:ℝ)..1, g x^2),
      sq_nonneg ((∫ x in z..z+l, g x)-Real.sqrt (l*∫ x in (0:ℝ)..1, g x^2))]
  have hdiff : (∫ x in z..z+l, g x) = (∫ x in z..z+l, |F x|)-l*c := by
    rw [show g = fun x => |F x|-c from rfl,intervalIntegral.integral_sub (hF.abs.intervalIntegrable _ _)
      intervalIntegrable_const,intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left]
  change _ ≤ c*l+Real.sqrt (l*∫ x in (0:ℝ)..1, g x^2)
  linarith

#print axioms cubic_lower
#print axioms integral_abs_unit
#print axioms periodic_window
end LengthGrowth.ActualFlow.FiniteSignIntegrals
