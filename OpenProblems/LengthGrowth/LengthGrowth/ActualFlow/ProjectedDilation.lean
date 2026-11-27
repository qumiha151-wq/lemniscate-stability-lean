import LengthGrowth.ActualFlow.WeightedForceRate

noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace LengthGrowth.ClosedFrenetCurve

/-- Ambient first variation in one Cartesian direction, for an arbitrary smooth
profile of that same coordinate. Taking the two coordinates gives a bounded
test field that agrees with dilation in the inner square. -/
theorem projected_dilation_identity (c : ClosedFrenetCurve) (l : ℂ →L[ℝ] ℝ)
    {v : ℝ → ℝ} (cv : ContDiff ℝ ∞ v) :
    (∫ s in 0..c.period, c.force s * l (c.normal s) * v (l (c.curve s))) =
    ∫ s in 0..c.period, c.curvature s * l (c.normal s) * l (c.tangent s)^2 *
        deriv (deriv v) (l (c.curve s)) +
      c.curvature s^2 * (l (c.normal s)^2 - 3/2 * l (c.tangent s)^2) *
        deriv v (l (c.curve s)) := by
  let h := fun s => l (c.curve s)
  let q := fun s => l (c.tangent s)
  let n := fun s => l (c.normal s)
  let k := c.curvature
  let j := c.curvature₁
  let F := c.force
  let w := fun s => v (h s)
  let a := fun s => deriv v (h s)
  let b := fun s => deriv (deriv v) (h s)
  let work := fun s => F s*n s*w s
  let area := fun s => k s*n s*q s^2*b s + k s^2*(n s^2-3/2*q s^2)*a s
  let flux := fun s => (k s^2/2*q s+j s*n s)*w s-k s*n s*q s*a s
  have dh (s : ℝ) : HasDerivAt h (q s) s :=
    l.hasFDerivAt.comp_hasDerivAt s (c.curve_deriv s)
  have dq (s : ℝ) : HasDerivAt q (k s*n s) s := by
    simpa only [q,n,k,normal,Function.comp_def,← Complex.real_smul,map_smul,smul_eq_mul] using
      l.hasFDerivAt.comp_hasDerivAt s (c.tangent_deriv s)
  have dn (s : ℝ) : HasDerivAt n (-(k s)*q s) s := by
    simpa only [q,n,k,Function.comp_def,←Complex.ofReal_neg,← Complex.real_smul,map_smul,smul_eq_mul]
      using l.hasFDerivAt.comp_hasDerivAt s (c.normal_deriv s)
  have ca0 := (contDiff_infty_iff_deriv.mp cv).2
  have cb0 := (contDiff_infty_iff_deriv.mp ca0).2
  have df (s : ℝ) : HasDerivAt flux (work s-area s) s := by
    have hw : HasDerivAt w (a s*q s) s := (cv.differentiable (by simp) _).hasDerivAt.comp s (dh s)
    have ha : HasDerivAt a (b s*q s) s := (ca0.differentiable (by simp) _).hasDerivAt.comp s (dh s)
    have hk := c.curvature_deriv s
    have hj := c.curvature₁_deriv s
    have first := (((((hk.pow 2).div_const 2).mul (dq s)).add (hj.mul (dn s))).mul hw)
    have last := (((hk.mul (dn s)).mul (dq s)).mul ha)
    apply (first.sub last).congr_deriv
    dsimp only [work,area,F,force,k,j,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  have cH := continuous_iff_continuousAt.mpr (fun s => (dh s).continuousAt)
  have cq := continuous_iff_continuousAt.mpr (fun s => (dq s).continuousAt)
  have cn := continuous_iff_continuousAt.mpr (fun s => (dn s).continuousAt)
  have cw : Continuous w := cv.continuous.comp cH
  have ca : Continuous a := ca0.continuous.comp cH
  have cb : Continuous b := cb0.continuous.comp cH
  have ck : Continuous k := c.curvature_continuous
  have cf : Continuous F := c.force_continuous
  have cwork : Continuous work := by dsimp only [work]; fun_prop
  have carea : Continuous area := by dsimp only [area]; fun_prop
  have int := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun s _ => df s) ((cwork.sub carea).intervalIntegrable _ _)
  have periodic : Function.Periodic flux c.period := by
    intro s
    simp only [flux,w,a,h,k,j,q,n,normal,c.curve_periodic s,c.curvature_periodic s,
      c.curvature₁_periodic s,c.tangent_periodic s]
  have ep : flux c.period=flux 0 := by simpa only [zero_add] using periodic 0
  rw [ep,sub_self,intervalIntegral.integral_sub (cwork.intervalIntegrable _ _)
    (carea.intervalIntegrable _ _)] at int
  exact sub_eq_zero.mp int

end LengthGrowth.ClosedFrenetCurve
#print axioms LengthGrowth.ClosedFrenetCurve.projected_dilation_identity
