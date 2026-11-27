import LengthGrowth.ActualFlow.CubicHalfThreshold
import Mathlib.Algebra.QuadraticDiscriminant

noncomputable section
open MeasureTheory Set
namespace LengthGrowth.ActualFlow

/-- A continuous distribution supported above -d gives a positive quadratic
moment form. The spatial weight can be the physical speed of the immersion. -/
theorem curvature_support_quadratic {k w : ℝ → ℝ} {P d L μ H : ℝ}
    (pp : 0 ≤ P) (lp : 0 < L) (hk : Continuous k) (hw : Continuous w)
    (wn : ∀ u, 0 ≤ w u) (hb : ∀ u, -d ≤ k u)
    (mass : (∫ u in 0..P, w u) = L)
    (mean : (∫ u in 0..P, k u*w u) = L*μ)
    (second : (∫ u in 0..P, k u^2*w u) = L)
    (third : (∫ u in 0..P, k u^3*w u) = L*H) :
    ∀ x : ℝ, 0 ≤ (μ+d)*(x*x) - 2*(1+d*μ)*x + H+d := by
  intro x
  have pos := intervalIntegral.integral_nonneg_of_forall (μ:=volume) pp (fun u =>
    mul_nonneg (mul_nonneg (show 0≤k u+d by linarith [hb u]) (sq_nonneg (k u-x))) (wn u))
  have eq : (∫ u in 0..P, (k u+d)*(k u-x)^2*w u) =
      L*((μ+d)*(x*x)-2*(1+d*μ)*x+H+d) := by
    calc
      _ = ∫ u in 0..P, k u^3*w u+(d-2*x)*(k u^2*w u)+
        (x^2-2*d*x)*(k u*w u)+(d*x^2)*w u := by
          apply intervalIntegral.integral_congr
          intro u _
          dsimp only
          ring
      _ = _ := by
        simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
          [intervalIntegral.integral_add, intervalIntegral.integral_const_mul]
        rw [mass,mean,second,third]
        ring
  rw [eq] at pos
  exact nonneg_of_mul_nonneg_right pos lp

/-- At a record, the centered force inequality and the moment form bound the
opposite curvature excursion in terms of the actual signed mean. -/
theorem signed_excursion_constraint {d μ H : ℝ}
    (mu : μ<1) (avg : 0≤μ+d) (force : 2*H≤1+μ)
    (pos : ∀ x : ℝ, 0≤(μ+d)*(x*x)-2*(1+d*μ)*x+H+d) :
    2+μ ≤ 2*(1+μ)*d^2 + d := by
  have disc := discrim_le_zero (a:=μ+d) (b:=-2*(1+d*μ)) (c:=H+d)
    (fun x => by linarith only [pos x])
  unfold discrim at disc
  have h : 0 ≤ (1-μ)*(2*(1+μ)*d^2+d-2-μ) := by
    nlinarith only [disc,mul_nonneg avg (sub_nonneg.mpr force)]
  linarith only [nonneg_of_mul_nonneg_right h (sub_pos.mpr mu)]

end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.curvature_support_quadratic
#print axioms LengthGrowth.ActualFlow.signed_excursion_constraint
