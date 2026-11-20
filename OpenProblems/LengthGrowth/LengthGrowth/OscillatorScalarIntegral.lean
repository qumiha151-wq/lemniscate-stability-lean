import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact reciprocal-quadratic quarter-period quadrature. -/
noncomputable section
namespace LengthGrowth.OscillatorMean
open Real Set MeasureTheory

private def ellipse (A B x : ℝ) := 1/(A^2*cos x^2+B^2*sin x^2)

private theorem ellipse_den_pos {A B : ℝ} (hA : 0<A) (hB : 0<B) (x : ℝ) :
    0<A^2*cos x^2+B^2*sin x^2 := by
  by_cases hz : cos x=0
  · have hs := sin_sq_add_cos_sq x
    have eq : sin x^2=1 := by rw [hz] at hs; linarith
    simpa only [hz,zero_pow (by decide : 2≠0),mul_zero,zero_add,eq,mul_one]
      using (show 0<B^2 from sq_pos_of_pos hB)
  · exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hA) (sq_pos_of_ne_zero hz))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))

private theorem ellipse_cont {A B : ℝ} (hA : 0<A) (hB : 0<B) : Continuous (ellipse A B) := by
  unfold ellipse
  apply Continuous.div continuous_const
  · fun_prop
  · exact fun x => (ellipse_den_pos hA hB x).ne'

private theorem first_quarter {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    (∫ x in 0..π/4,ellipse A B x) = arctan (B/A)/(A*B) := by
  let f : ℝ → ℝ := fun x => arctan ((B/A)*tan x)/(A*B)
  have d (x : ℝ) (hx : x∈uIcc 0 (π/4)) : HasDerivAt f (ellipse A B x) x := by
    rw [uIcc_of_le (by positivity)] at hx
    have hp := pi_pos
    have hcos : 0<cos x := cos_pos_of_mem_Ioo ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hd := (((Real.hasDerivAt_tan hcos.ne').const_mul (B/A)).arctan).div_const (A*B)
    have e : (1/(1+((B/A)*tan x)^2)*((B/A)*(1/cos x^2)))/(A*B) = ellipse A B x := by
      rw [tan_eq_sin_div_cos]
      dsimp [ellipse]
      field_simp [hcos.ne',hA.ne',hB.ne', (ellipse_den_pos hA hB x).ne']
    exact e ▸ hd
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt d
    ((ellipse_cont hA hB).intervalIntegrable 0 (π/4))
  simpa [f,Real.tan_pi_div_four] using h

theorem reciprocal_quarter_integral {A B : ℝ} (hA : 0<A) (hB : 0<B) :
    (∫ x in 0..π/2,1/(A^2*cos x^2+B^2*sin x^2)) = π/(2*A*B) := by
  have h1 := first_quarter hA hB
  have h2 := first_quarter hB hA
  have ref : (fun x => ellipse A B (π/2-x)) = ellipse B A := by
    funext x
    simp only [ellipse,cos_pi_div_two_sub,sin_pi_div_two_sub,add_comm]
  have sub := intervalIntegral.integral_comp_sub_left (a:=0) (b:=π/4) (ellipse A B) (π/2)
  rw [ref,show π/2-π/4=π/4 by ring,sub_zero] at sub
  have both := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    ((ellipse_cont hA hB).intervalIntegrable 0 (π/4))
    ((ellipse_cont hA hB).intervalIntegrable (π/4) (π/2))
  change (∫ x in 0..π/2,ellipse A B x) = _
  rw [← both,h1,← sub,h2,show A/B=(B/A)⁻¹ by rw [inv_div],arctan_inv_of_pos (div_pos hB hA)]
  field_simp [hA.ne',hB.ne']
  ring

theorem baseline_integral_exact :
    (∫ x in 0..π/2,(4-7*cos x^2)/(4+7*cos x^2)) = π*(2/√11-1/2) := by
  have hs : (√(11:ℝ))^2=11 := sq_sqrt (by norm_num)
  have h := reciprocal_quarter_integral (A:=√11) (B:=2) (by positivity) (by norm_num)
  have hfun : (fun x => 1/((√11)^2*cos x^2+(2:ℝ)^2*sin x^2)) =
      (fun x => 1/(4+7*cos x^2)) := by
    funext x
    rw [hs]
    congr 1
    nlinarith [sin_sq_add_cos_sq x]
  rw [hfun] at h
  have cont : Continuous (fun x : ℝ => 1/(4+7*cos x^2)) := by
    apply Continuous.div continuous_const
    · fun_prop
    · intro x
      positivity
  have eqf : (fun x : ℝ => (4-7*cos x^2)/(4+7*cos x^2)) =
      (fun x : ℝ => 8*(1/(4+7*cos x^2))-1) := by
    funext x
    field_simp [show (4+7*cos x^2)≠0 by positivity]
    ring
  rw [eqf,intervalIntegral.integral_sub ((cont.const_mul 8).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const,h]
  simp only [sub_zero,smul_eq_mul,mul_one]
  field_simp [show √(11:ℝ)≠0 by positivity]
  ring

end LengthGrowth.OscillatorMean
