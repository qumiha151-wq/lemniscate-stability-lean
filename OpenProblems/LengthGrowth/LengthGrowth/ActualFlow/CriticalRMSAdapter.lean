import LengthGrowth.ActualFlow.StrictHalfTransfer
import LengthGrowth.ActualFlow.ArclengthIntegrals

/-! Actual arclength and RMS curvature normalization of periodic material positions. -/
noncomputable section
open MeasureTheory Function
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- The scalar statement on arbitrary smooth periodic functions, expressed
using ordinary real-line derivatives and unweighted interval averages. -/
def ScalarStrictHalfGap (ε : ℝ) : Prop :=
  ∀ (P : ℝ) (u : ℝ → ℝ), 0<P → ContDiff ℝ ∞ u → Periodic u P →
    let av := fun f : ℝ → ℝ => (∫ x in 0..P, f x)/P
    let v := fun x => deriv (deriv u) x + (1/2:ℝ)*(u x)^3
    av (fun x => u x^2)=1 → |av u|≤ε →
    av (fun x => v x^2)-(1/2:ℝ)*av (fun x => u x*v x)≤ε →
    |av (fun x => u x^3)| ≤ 1/2-ε

namespace PeriodicRegularPosition
variable (c : PeriodicRegularPosition)

def scaledArclengthCurvature (a t : ℝ) : ℝ := a*c.closedFrenetCurve.curvature (a*t)

private theorem arc_k_smooth : ContDiff ℝ ∞ c.closedFrenetCurve.curvature :=
  LengthGrowth.position_curvature_smooth c.unitSpeedPosition_smooth

theorem scaledArclengthCurvature_smooth (a : ℝ) : ContDiff ℝ ∞ (c.scaledArclengthCurvature a) :=
  contDiff_const.mul (c.arc_k_smooth.comp (contDiff_const.mul contDiff_id))

theorem scaledArclengthCurvature_periodic {a P : ℝ} (h : a*P=c.length) :
    Periodic (c.scaledArclengthCurvature a) P := by
  intro t
  unfold scaledArclengthCurvature
  rw [mul_add,h]
  exact congrArg (a * ·) (c.closedFrenetCurve.curvature_periodic (a*t))

theorem scaledArclengthCurvature_force (a t : ℝ) :
    deriv (deriv (c.scaledArclengthCurvature a)) t+
      (1/2:ℝ)*c.scaledArclengthCurvature a t ^ 3 =
      a^3*c.closedFrenetCurve.force (a*t) := by
  let k := c.closedFrenetCurve.curvature
  have hk : Differentiable ℝ k := c.arc_k_smooth.differentiable (by simp)
  have hk' : Differentiable ℝ (deriv k) := (contDiff_infty_iff_deriv.mp c.arc_k_smooth).2.differentiable (by simp)
  have h1 : deriv (c.scaledArclengthCurvature a) = fun y => a^2 * deriv k (a*y) := by
    funext y
    have h := ((((hk (a*y)).hasDerivAt).comp y ((hasDerivAt_id y).const_mul a)).const_mul a).deriv
    change deriv (fun y => a*k (a*y)) y = _
    calc
      _ = a*(deriv k (a*y)*(a*1)) := h
      _ = _ := by ring
  rw [h1]
  have h2 := ((((hk' (a*t)).hasDerivAt).comp t ((hasDerivAt_id t).const_mul a)).const_mul (a^2)).deriv
  have h2' : deriv (fun y => a^2*deriv k (a*y)) t = a^2*(deriv (deriv k) (a*t)*(a*1)) := h2
  rw [h2']
  change _+(1/2:ℝ)*(a*k (a*t))^3=a^3*(deriv (deriv k) (a*t)+k (a*t)^3/2)
  ring

/-- Every mixed moment of the rescaled curvature and its actual second-order
force equals the matching material moment with its arclength density. -/
theorem scaledArclengthCurvature_moment {a P : ℝ} (ha : 0<a) (hP : 0<P)
    (h : a*P=c.length) (i j : ℕ) :
    let u := c.scaledArclengthCurvature a
    let v := fun t => deriv (deriv u) t + (1/2:ℝ)*u t^3
    (∫ t in 0..P, u t^i * v t^j)/P =
      (a^i*(a^3)^j/c.length) * ∫ s in 0..c.period,
        curvature c.position s^i * force c.position s^j * speed c.position s := by
  dsimp only
  let f (s : ℝ) := curvature c.position s^i * force c.position s^j
  have hf : Continuous f :=
    ((curvature_smooth c.smooth c.regular).continuous.pow i).mul
      ((force_smooth c.smooth c.regular).continuous.pow j)
  have heq : (fun t => (c.scaledArclengthCurvature a t)^i *
      (deriv (deriv (c.scaledArclengthCurvature a)) t+(1/2:ℝ)*(c.scaledArclengthCurvature a t)^3)^j) =
      fun t => (a^i*(a^3)^j)*f (c.arclengthInverse (a*t)) := by
    funext t
    rw [c.scaledArclengthCurvature_force,scaledArclengthCurvature,
      c.closedFrenetCurve_curvature,c.closedFrenetCurve_force,mul_pow,mul_pow]
    dsimp only [f]
    ring
  rw [heq,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun y => f (c.arclengthInverse y)) ha.ne',
    mul_zero,h,smul_eq_mul,c.integral_comp_inverse hf]
  change _=(a^i*(a^3)^j/c.length)*(∫ s in 0..c.period, f s*speed c.position s)
  rw [← h]
  field_simp [ha.ne',hP.ne']

end PeriodicRegularPosition

/-- The material-coordinate gap follows from the scalar universal estimate.
The period is the square root of twice the actual energy-length product. -/
theorem strictHalfSliceGap_of_scalar {ε : ℝ} (scalar : ScalarStrictHalfGap ε) :
    StrictHalfSliceGap ε := by
  intro c
  let E := materialEnergy c.position c.period
  let L := c.length
  let P := Real.sqrt (2*(E*L))
  let a := L/P
  let u := c.scaledArclengthCurvature a
  let v := fun t => deriv (deriv u) t+(1/2:ℝ)*u t^3
  let avg := fun f : ℝ → ℝ => (∫ t in 0..P, f t)/P
  let S := materialSignedCurvature c.position c.period
  let C := materialCubicCurvature c.position c.period
  let D := materialDissipation c.position c.period
  let V := materialLengthRate c.position c.period
  have hL : 0<L := c.length_pos
  have hE : 0<E := c.material_energy_pos
  have hb : 0<2*(E*L) := by positivity
  have hP : 0<P := Real.sqrt_pos.mpr hb
  have hp2 : P^2=2*(E*L) := Real.sq_sqrt hb.le
  have hE' : E=P^2/(2*L) := by
    apply (eq_div_iff (by positivity : (2:ℝ)*L ≠ 0)).mpr
    linarith only [hp2]
  have ha : 0<a := div_pos hL hP
  have hap : a*P=c.length := div_mul_cancel₀ L hP.ne'
  change |S|/P≤ε → L^4*(L*D-E*V)≤ε*(2*(E*L))^3 → |L*C/(2*E*P)|≤1/2-ε
  intro hS hloss
  have moment := c.scaledArclengthCurvature_moment ha hP hap
  have one := moment 1 0
  have two := moment 2 0
  have three := moment 3 0
  have vv := moment 0 2
  have uv := moment 1 1
  simp only [pow_zero,pow_one,one_mul,mul_one] at one two three vv uv
  change avg u = a/L*S at one
  change avg (fun t => u t^2) = a^2/L*(∫ s in 0..c.period, curvature c.position s^2*speed c.position s) at two
  change avg (fun t => u t^3) = a^3/L*C at three
  change avg (fun t => v t^2) = (a^3)^2/L*D at vv
  change avg (fun t => u t*v t) = a*a^3/L*V at uv
  have eint : (∫ s in 0..c.period, curvature c.position s^2*speed c.position s)=2*E := by
    dsimp only [E,materialEnergy]
    ring
  have unit : avg (fun t => u t^2)=1 := by
    rw [two,eint,hE']
    dsimp only [a]
    field_simp [hL.ne',hP.ne']
  have signed : |avg u|≤ε := by
    rw [one,show a/L*S=S/P by dsimp only [a]; field_simp [hL.ne',hP.ne'],abs_div,abs_of_pos hP]
    exact hS
  have loss : avg (fun t => v t^2)-(1/2:ℝ)*avg (fun t => u t*v t)≤ε := by
    rw [vv,uv]
    have eqn : (a^3)^2/L*D-(1/2:ℝ)*(a*a^3/L*V)=L^4*(L*D-E*V)/(P^2)^3 := by
      dsimp only [a]
      rw [hE']
      field_simp [hL.ne',hP.ne']
    rw [eqn,hp2]
    exact (div_le_iff₀ (by positivity)).mpr hloss
  have bound := scalar P u hP (c.scaledArclengthCurvature_smooth a)
    (c.scaledArclengthCurvature_periodic hap) unit signed loss
  change |avg (fun t => u t^3)| ≤ 1/2-ε at bound
  rw [three] at bound
  have ratio : L*C/(2*E*P)=a^3/L*C := by
    dsimp only [a]
    rw [hE']
    field_simp [hL.ne',hP.ne']
  rwa [ratio]

#print axioms PeriodicRegularPosition.scaledArclengthCurvature_force
#print axioms PeriodicRegularPosition.scaledArclengthCurvature_moment
#print axioms strictHalfSliceGap_of_scalar
end LengthGrowth.ActualFlow
