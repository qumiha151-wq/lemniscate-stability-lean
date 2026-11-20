import LengthGrowth.ActualFlow.FiniteSignWindow

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.FiniteSignWindow

theorem residual_mass (F : ℝ→ℝ) (hF : Continuous F) (c : ℝ) :
    (∫s in (0:ℝ)..1,(|F s|-c)^2)=(∫s in (0:ℝ)..1,F s^2)-2*c*(∫s in (0:ℝ)..1,|F s|)+c^2 := by
  have he (s:ℝ) : (|F s|-c)^2=(F s^2-2*c*|F s|)+c^2 := by nlinarith only [sq_abs (F s)]
  simp_rw [he]
  rw [intervalIntegral.integral_add (f:=fun s=>F s^2-2*c*|F s|) (g:=fun _=>c^2)
    (((hF.pow 2).sub (hF.abs.const_mul (2*c))).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_sub (f:=fun s=>F s^2) (g:=fun s=>2*c*|F s|) ((hF.pow 2).intervalIntegrable _ _)
      ((hF.abs.const_mul (2*c)).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  simp

theorem amplitude_budget {a P m c R : ℝ} (ha : 0<a) (hP : 0<P) (hm : 1≤m)
    (hc : 0≤c) (_hR : 0≤R) (hr : R≤4*c*m*a^2)
    (cost : a^2/4 < c*(P/a)+Real.sqrt ((P/a)*R)) : a^3 < 256*P*m*c := by
  by_contra! high
  have hm0:0≤m:=by linarith
  have tone : c*(P/a) ≤ a^2/256 := by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ ha).mpr
    nlinarith only [high,mul_nonneg (mul_nonneg hP.le hc) (sub_nonneg.mpr hm)]
  have hsq : (P/a)*R ≤ (a^2/8)^2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hr hP.le,
      mul_le_mul_of_nonneg_right high (sq_nonneg a)]
  have ht : Real.sqrt ((P/a)*R)≤a^2/8 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hsq⟩
  nlinarith only [tone,ht,cost,sq_nonneg a]

end LengthGrowth.ActualFlow.FiniteSignWindow
#print axioms LengthGrowth.ActualFlow.FiniteSignWindow.amplitude_budget
