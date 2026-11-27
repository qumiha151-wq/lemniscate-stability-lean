import LengthGrowth.ActualFlow.DefectThirtySix

noncomputable section
open MeasureTheory
namespace LengthGrowth.BendingSublevel

/-- Exact centered second, third, and fourth moments of a continuous real
function on the period, retaining the full signed third moment. -/
theorem centered_moments {P μ : ℝ} {k : ℝ → ℝ} (ck : Continuous k)
    (mean : (∫ s in 0..P,k s)=P*μ) :
    let u := fun s => k s-μ
    let V := ∫ s in 0..P,u s^2
    let I₃ := ∫ s in 0..P,u s^3
    (∫ s in 0..P,u s)=0 ∧
    (∫ s in 0..P,k s^2)=P*μ^2+V ∧
    (∫ s in 0..P,k s^3)=P*μ^3+3*μ*V+I₃ ∧
    (∫ s in 0..P,k s^4)=P*μ^4+6*μ^2*V+4*μ*I₃+(∫ s in 0..P,u s^4) := by
  let u := fun s => k s-μ
  have cu : Continuous u := ck.sub continuous_const
  have avg : (∫ s in 0..P,u s)=0 := by
    dsimp only [u]
    rw [intervalIntegral.integral_sub (ck.intervalIntegrable 0 P)
      (continuous_const.intervalIntegrable 0 P),intervalIntegral.integral_const,mean]
    simp
  have h2 (s : ℝ) : k s^2=μ^2+2*μ*u s+u s^2 := by dsimp [u]; ring
  have h3 (s : ℝ) : k s^3=μ^3+(3*μ^2)*u s+(3*μ)*u s^2+u s^3 := by dsimp [u]; ring
  have h4 (s : ℝ) : k s^4=μ^4+(4*μ^3)*u s+(6*μ^2)*u s^2+(4*μ)*u s^3+u s^4 := by dsimp [u]; ring
  refine ⟨avg,?_,?_,?_⟩
  · change (∫ s in 0..P,k s^2) = P*μ^2+∫ s in 0..P,u s^2
    simp_rw [h2]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
      [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg]
  · change (∫ s in 0..P,k s^3) = P*μ^3+3*μ*(∫ s in 0..P,u s^2)+∫ s in 0..P,u s^3
    simp_rw [h3]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
      [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg]
  · change (∫ s in 0..P,k s^4) = P*μ^4+6*μ^2*(∫ s in 0..P,u s^2)+
      4*μ*(∫ s in 0..P,u s^3)+∫ s in 0..P,u s^4
    simp_rw [h4]
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) ..)
      [intervalIntegral.integral_add,intervalIntegral.integral_const_mul,avg]

/-- The derivative variance is positive when a genuine, centered curvature
has nonzero variance. The constant-test and fourth-moment bounds avoid any
nondegeneracy hypothesis on the locations of its extrema. -/
theorem positive_gradient_of_variance (c : ClosedFrenetCurve) (μ : ℝ)
    (avg : (∫ s in 0..c.period,c.curvature s-μ)=0)
    (var : 0 < ∫ s in 0..c.period,(c.curvature s-μ)^2) : 0<c.curvatureGradientSquare := by
  let u := fun s => c.curvature s-μ
  have cu : Continuous u := c.curvature_continuous.sub continuous_const
  have bound := curvature_fourth_moment c μ avg
  have cs := interval_integral_mul_sq_le (f:=fun _ : ℝ => (1:ℝ))
    continuous_const (cu.pow 2) c.period_pos.le
  have cs' : (∫ s in 0..c.period,u s^2)^2 ≤ c.period*(∫ s in 0..c.period,u s^4) := by
    simpa [one_mul,←pow_mul] using cs
  have i4 : 0 < ∫ s in 0..c.period,u s^4 := by
    exact pos_of_mul_pos_right ((sq_pos_of_pos var).trans_le cs') c.period_pos.le
  change 3*(∫ s in 0..c.period,u s^4)^2 ≤
    (∫ s in 0..c.period,u s^2)^3*c.curvatureGradientSquare at bound
  exact pos_of_mul_pos_right ((show 0<3*(∫ s in 0..c.period,u s^4)^2 by positivity).trans_le bound)
    (pow_nonneg var.le _)

end LengthGrowth.BendingSublevel
#print axioms LengthGrowth.BendingSublevel.centered_moments
#print axioms LengthGrowth.BendingSublevel.positive_gradient_of_variance
