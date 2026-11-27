import LengthGrowth.ActualFlow.TangentFourierMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
namespace LengthGrowth.TangentSpectrum
noncomputable section
open Real Set MeasureTheory

/-- On the unit arclength interval, integrate the Frenet identity and the
true cubic force, preserving the sign of the length derivative at a record. -/
theorem second_tangent_estimate {K B C : ℝ→ℝ} {A : ℝ→ℂ} {X : ℝ}
    (xp : 0<X) (kd : ∀x,HasDerivAt K (B x) x) (bd : ∀x,HasDerivAt B (C x) x)
    (cc : Continuous C) (p : K 1=K 0) (p1 : B 1=B 0)
    (speed : ∀x,‖A x‖^2=B x^2+K x^4)
    (mass : (∫x in 0..1,K x^2)=2*X^3)
    (stress : ∀x,|K x|^6≤(2^25:ℝ)*X^12)
    (work : 0≤∫x in 0..1,K x*(C x+K x^3/2)) :
    (∫x in 0..1,‖A x‖^2)≤1024*X^7 := by
  have ck : Continuous K := continuous_iff_continuousAt.mpr fun x=>(kd x).continuousAt
  have cb : Continuous B := continuous_iff_continuousAt.mpr fun x=>(bd x).continuousAt
  have integr (f : ℝ→ℝ) (cf : Continuous f) : IntervalIntegrable f volume 0 1 := cf.intervalIntegrable _ _
  have d (x : ℝ) : HasDerivAt (fun y=>K y*B y) (B x^2+K x*C x) x := by simpa only [pow_two] using (kd x).fun_mul (bd x)
  have ad := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (fun x _=>d x)
    (integr _ ((cb.pow 2).add (ck.mul cc)))
  rw [p,p1,sub_self,intervalIntegral.integral_add (f:=fun x=>B x^2) (g:=fun x=>K x*C x) (integr _ (cb.pow 2)) (integr _ (ck.mul cc))] at ad
  have hf : (∫x in (0:ℝ)..1,K x*(C x+K x^3/2)) =
      (∫x in (0:ℝ)..1,K x*C x)+(1/2:ℝ)*(∫x in (0:ℝ)..1,K x^4) := by
    have eq (x : ℝ) : K x*(C x+K x^3/2)=K x*C x+(1/2)*K x^4 := by ring
    simp_rw [eq]
    rw [intervalIntegral.integral_add (f:=fun x=>K x*C x) (g:=fun x=>(1/2:ℝ)*K x^4) (integr _ (ck.mul cc)) (integr _ (continuous_const.mul (ck.pow 4))),intervalIntegral.integral_const_mul]
  rw [hf] at work
  have intA : (∫x in (0:ℝ)..1,‖A x‖^2)=(∫x in (0:ℝ)..1,B x^2)+(∫x in (0:ℝ)..1,K x^4) := by
    simp_rw [speed]
    exact intervalIntegral.integral_add (f:=fun x=>B x^2) (g:=fun x=>K x^4) (integr _ (cb.pow 2)) (integr _ (ck.pow 4))
  have pt (x : ℝ) : K x^4≤(340*X^4)*(K x^2) := by
    have h : (K x^2)^3≤(340*X^4)^3 := by
      have g := stress x
      rw [←abs_pow,abs_of_nonneg (Even.pow_nonneg (by decide : Even 6) _)] at g
      have h := mul_le_mul_of_nonneg_right (by norm_num : (2^25:ℝ)≤340^3) (pow_nonneg xp.le 12)
      nlinarith only [g,h]
    have q := (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) (by decide : (3:ℕ)≠0)).mp h
    exact (show K x^4=K x^2*K x^2 by ring).le.trans (mul_le_mul_of_nonneg_right q (sq_nonneg _))
  have b := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ)≤1) (integr _ (ck.pow 4))
    (integr _ (continuous_const.mul (ck.pow 2))) (fun x _=>pt x)
  change (∫x in (0:ℝ)..1,K x^4)≤∫x in (0:ℝ)..1,(340*X^4)*K x^2 at b
  rw [intervalIntegral.integral_const_mul,mass] at b
  nlinarith only [intA,ad,work,b,pow_pos xp 7]

end
end LengthGrowth.TangentSpectrum
#print axioms LengthGrowth.TangentSpectrum.second_tangent_estimate
