import LengthGrowth.ActualFlow.ForceMaterialEquation

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow

/-- The weak form of the dissipation derivative, after moving derivatives
off the material curvature rate using spatial periodicity. -/
def forceVariationDensity (x : ℝ → ℂ) (u : ℝ) : ℝ :=
  let k := curvature x u
  let F := force x u
  let Fs := arcDerivative x (force x)
  ((2*arcDerivative x Fs u+3*k^2*F)*bendingRate x u +
    2*Fs u*k*F*curvatureGradient x u-2*k*F^2*curvatureSecond x u+k*F^3)*speed x u

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem force_dissipation_variation (flow : c.IsNormalFEF) {t : ℝ} (ht : t∈I) :
    HasDerivAt c.dissipation (∫ u in 0..c.period, forceVariationDensity (c.position t) u) t := by
  let x := c.position t
  let g := speed x
  let k := curvature x
  let ks := curvatureGradient x
  let F := force x
  let Fs := arcDerivative x F
  let Fss := arcDerivative x Fs
  let V := bendingRate x
  let W := bendingGradientRate x
  let flux := fun u => 2*(F u*W u-Fs u*V u)
  have sm := c.position_slice_smooth ht
  have reg := c.immersion t ht
  have per := c.periodic t ht
  have cg : ContDiff ℝ ∞ g := speed_smooth sm reg
  have ck : ContDiff ℝ ∞ k := curvature_smooth sm reg
  have cks : ContDiff ℝ ∞ ks := curvatureGradient_smooth sm reg
  have cf : ContDiff ℝ ∞ F := force_smooth sm reg
  have cs : ContDiff ℝ ∞ Fs := arcDerivative_smooth sm reg cf
  have c2 : ContDiff ℝ ∞ Fss := arcDerivative_smooth sm reg cs
  have cv : ContDiff ℝ ∞ V := c2.neg.sub ((ck.pow 2).mul cf)
  have cxv : ContDiff ℝ ∞ (arcDerivative x V) := arcDerivative_smooth sm reg cv
  have cw : ContDiff ℝ ∞ W := cxv.sub (((ck.mul cf).mul cks))
  have cflux : ContDiff ℝ ∞ flux := by dsimp only [flux]; fun_prop
  have cdens : Continuous (forceVariationDensity x) := by
    change Continuous (fun u => ((2*Fss u+3*(k u)^2*F u)*V u+
      2*Fs u*k u*F u*ks u-2*k u*(F u)^2*curvatureSecond x u+k u*(F u)^3)*g u)
    have cks₂ := curvatureSecond_smooth sm reg
    fun_prop
  have pf : Function.Periodic F c.period := force_periodic sm reg per
  have pk : Function.Periodic k c.period := curvature_periodic sm reg per
  have pks : Function.Periodic ks c.period := curvatureGradient_periodic sm reg per
  have ps : Function.Periodic Fs c.period := arcDerivative_periodic sm per (cf.differentiable (by simp)) pf
  have pss : Function.Periodic Fss c.period := arcDerivative_periodic sm per (cs.differentiable (by simp)) ps
  have pv : Function.Periodic V c.period := by
    intro u
    change -Fss (u+c.period)-k (u+c.period)^2*F (u+c.period)= -Fss u-k u^2*F u
    rw [pss,pk,pf]
  have pdv := arcDerivative_periodic sm per (cv.differentiable (by simp)) pv
  have pw : Function.Periodic W c.period := by
    intro u
    change arcDerivative x V (u+c.period)-k (u+c.period)*F (u+c.period)*ks (u+c.period)=_
    rw [pdv,pk,pf,pks]
    rfl
  have pflux : Function.Periodic flux c.period := by
    intro u
    dsimp only [flux]
    rw [pf,pw,ps,pv]
  have dfc := (contDiff_infty_iff_deriv.mp cflux).2.continuous
  have fluxInt := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => (cflux.differentiable (by simp) u).hasDerivAt) (dfc.intervalIntegrable ..)
  have endpoints : flux c.period = flux 0 := by simpa only [zero_add] using pflux 0
  rw [endpoints,sub_self] at fluxInt
  have time := hasDerivAt_intervalIntegral_of_jointC1 (a:=0) (b:=c.period) (F:=fun v u =>
    force (c.position v) u ^ 2 * speed (c.position v) u) c.time_open
    (((c.force_joint_smooth.pow 2).mul c.speed_joint_smooth).of_le (by simp)) ht
  have derivative (u) : deriv (fun v => force (c.position v) u ^ 2 * speed (c.position v) u) t =
      forceVariationDensity x u + deriv flux u := by
    have dr := ((c.elastic_force_material_rate flow ht u).pow 2).mul (c.speed_time_hasDerivAt ht u)
    change HasDerivAt (fun v => force (c.position v) u ^ 2 * speed (c.position v) u) _ t at dr
    rw [dr.deriv,(c.arcTurn_frameRate flow ht u).2]
    have dF : HasDerivAt F (g u*Fs u) u :=
      hasDerivAt_speed_smul_arcDerivative reg (cf.differentiable (by simp)) u
    have dFs : HasDerivAt Fs (g u*Fss u) u :=
      hasDerivAt_speed_smul_arcDerivative reg (cs.differentiable (by simp)) u
    have dV : HasDerivAt V (g u*arcDerivative x V u) u :=
      hasDerivAt_speed_smul_arcDerivative reg (cv.differentiable (by simp)) u
    have dW : HasDerivAt W (g u*arcDerivative x W u) u :=
      hasDerivAt_speed_smul_arcDerivative reg (cw.differentiable (by simp)) u
    have fluxD := ((dF.mul dW).sub (dFs.mul dV)).const_mul 2
    change HasDerivAt flux _ u at fluxD
    rw [fluxD.deriv]
    change 2*F u^(2-1)*(arcDerivative x W u-k u*F u*curvatureSecond x u+
      3/2*k u^2*V u)*g u+F u^2*(g u*(k u*F u))= _
    change _ = ((2*Fss u+3*k u^2*F u)*V u+2*Fs u*k u*F u*ks u-
      2*k u*F u^2*curvatureSecond x u+k u*F u^3)*g u+
      2*(g u*Fs u*W u+F u*(g u*arcDerivative x W u)-
      (g u*Fss u*V u+Fs u*(g u*arcDerivative x V u)))
    rw [show W u=arcDerivative x V u-k u*F u*ks u from rfl]
    ring
  have eqn := funext derivative
  rw [eqn,intervalIntegral.integral_add (cdens.intervalIntegrable ..) (dfc.intervalIntegrable ..),
    fluxInt,add_zero] at time
  exact time

end SmoothPeriodicImmersion
end LengthGrowth.ActualFlow
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.force_dissipation_variation
