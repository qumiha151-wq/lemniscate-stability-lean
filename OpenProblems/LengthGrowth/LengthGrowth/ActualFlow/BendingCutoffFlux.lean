import LengthGrowth.ActualFlow.MaterialTurnFlux

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Physical bending energy weighted by a scalar function of one Cartesian projection. -/
def projectedBendingMass (l : ℂ →L[ℝ] ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..c.period, f (l (c.position t u)) *
    (curvature (c.position t) u ^ 2 / 2) * speed (c.position t) u

theorem projectedBendingMass_material (hf : c.IsNormalFEF) (l : ℂ →L[ℝ] ℝ)
    {f : ℝ → ℝ} (cf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (c.projectedBendingMass l f)
      (∫ u in 0..c.period, -(deriv f (l (c.position t u))) *
          l (normal (c.position t) u) * force (c.position t) u *
          (curvature (c.position t) u ^ 2 / 2) * speed (c.position t) u +
        f (l (c.position t u)) * (curvature (c.position t) u *
          deriv (c.velocityGradientNormal t) u - curvature (c.position t) u ^ 2 / 2 *
          (speed (c.position t) u * c.velocityGradientTangent t u))) t := by
  let w := fun x u => f (l (c.position x u))
  let k := fun x => curvature (c.position x)
  let g := fun x => speed (c.position x)
  have wl : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => l (c.position z.1 z.2)) (I ×ˢ univ) :=
    l.contDiff.comp_contDiffOn c.joint_smooth
  have ws : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => w z.1 z.2) (I ×ˢ univ) :=
    cf.comp_contDiffOn wl
  have ks := c.curvature_joint_smooth
  have gs := c.speed_joint_smooth
  have sm : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => w z.1 z.2*(k z.1 z.2^2/2)*g z.1 z.2)
      (I ×ˢ univ) := (ws.mul ((ks.pow 2).div_const 2)).mul gs
  have h := hasDerivAt_intervalIntegral_of_jointC1 (a:=0) (b:=c.period)
    (F:=fun x u => w x u*(k x u^2/2)*g x u) c.time_open (sm.of_le (by simp)) ht
  apply h.congr_deriv
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have hd := l.hasFDerivAt.comp_hasDerivAt t (hf t ht u)
  have hh : HasDerivAt (fun x => l (c.position x u))
      (-force (c.position t) u*l (normal (c.position t) u)) t := by
    simpa only [Function.comp_def, ← Complex.ofReal_neg, ← Complex.real_smul,
      map_smul,smul_eq_mul] using hd
  have hw := (cf.differentiable (by simp) _).hasDerivAt.comp t hh
  have hk := joint_smooth_time_hasDerivAt c.time_open (f:=k) ks ht u
  have hg := c.speed_time_hasDerivAt ht u
  have prod := (hw.mul ((hk.pow 2).div_const 2)).mul hg
  change deriv (fun x => w x u*(k x u^2/2)*g x u) t = _
  rw [show deriv (fun x => w x u*(k x u^2/2)*g x u) t = _ from prod.deriv]
  dsimp [k,g,w]
  linear_combination (f (l (c.position t u)) * curvature (c.position t) u) *
    c.curvature_metric_rate_identity ht u

/-- Weighted physical energy law after all force derivatives have been integrated by parts. -/
theorem projectedBendingMass_flux (hf : c.IsNormalFEF) (l : ℂ →L[ℝ] ℝ)
    {f : ℝ → ℝ} (cf : ContDiff ℝ ∞ f) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (c.projectedBendingMass l f)
      (∫ u in 0..c.period, let x := c.position t; let h := l (x u)
        let q := l (tangent x u); let n := l (normal x u)
        let k := curvature x u; let j := curvatureGradient x u; let F := force x u
        (-f h * F^2 - F * (deriv (deriv f) h * q^2 * k +
          3 / 2 * deriv f h * n * k^2 + 2 * deriv f h * q * j)) * speed x u) t := by
  let x := c.position t
  let k := curvature x
  let j := curvatureGradient x
  let F := force x
  let g := speed x
  let p := arcDerivative x F
  let h := fun u => l (x u)
  let q := fun u => l (tangent x u)
  let n := fun u => l (normal x u)
  let w := fun u => f (h u)
  let a := fun u => deriv f (h u)
  let b := fun u => deriv (deriv f) (h u)
  let time := fun u => -a u*n u*F u*(k u^2/2)*g u +
    w u*(k u*deriv (c.velocityGradientNormal t) u -
      k u^2/2*(g u*c.velocityGradientTangent t u))
  let rate := fun u => (-w u * F u^2 - F u * (b u * q u^2 * k u +
    3/2 * a u * n u * k u^2 + 2 * a u * q u * j u)) * g u
  let flux := fun u => -(w u*k u)*p u+(a u*q u*k u+w u*j u)*F u
  have reg := c.immersion t ht
  have smooth := c.position_slice_smooth ht
  have per := c.periodic t ht
  have ck := curvature_smooth smooth reg
  have cj := curvatureGradient_smooth smooth reg
  have cF := force_smooth smooth reg
  have cp := arcDerivative_smooth smooth reg cF
  have cg := speed_smooth smooth reg
  have ct := tangent_smooth smooth reg
  have cn := normal_smooth smooth reg
  have ch : ContDiff ℝ ∞ h := l.contDiff.comp smooth
  have ca0 := (contDiff_infty_iff_deriv.mp cf).2
  have cb0 := (contDiff_infty_iff_deriv.mp ca0).2
  have cw : ContDiff ℝ ∞ w := cf.comp ch
  have ca : ContDiff ℝ ∞ a := ca0.comp ch
  have cb : ContDiff ℝ ∞ b := cb0.comp ch
  have cq : ContDiff ℝ ∞ q := l.contDiff.comp ct
  have cnn : ContDiff ℝ ∞ n := l.contDiff.comp cn
  have gN := joint_smooth_space_slice (f:=c.velocityGradientNormal) c.velocityGradientNormal_joint_smooth ht
  have gT := joint_smooth_space_slice (f:=c.velocityGradientTangent) c.velocityGradientTangent_joint_smooth ht
  have cdN := (contDiff_infty_iff_deriv.mp gN).2.continuous
  have cflux : ContDiff ℝ ∞ flux := by dsimp only [flux]; fun_prop
  have crate : Continuous rate := by dsimp only [rate]; fun_prop
  have hdflux := (contDiff_infty_iff_deriv.mp cflux).2.continuous
  have ps := arcDerivative_periodic smooth per (cF.differentiable (by simp)) (force_periodic smooth reg per)
  have periodic : Function.Periodic flux c.period := by
    intro u
    simp only [flux,w,a,h,q,k,j,F,p,x,per u,tangent_periodic smooth per u,
      curvature_periodic smooth reg per u,curvatureGradient_periodic smooth reg per u,
      force_periodic smooth reg per u,ps u]
  have zero := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=c.period)
    (fun u _ => (cflux.differentiable (by simp) u).hasDerivAt) (hdflux.intervalIntegrable _ _)
  have ep : flux c.period=flux 0 := by simpa only [zero_add] using periodic 0
  rw [ep,sub_self] at zero
  have neqn : c.velocityGradientNormal t=fun u => -p u :=
    funext (fun u => (c.arcTurn_frameRate hf ht u).1)
  have point (u : ℝ) : time u = rate u + deriv flux u := by
    have hk := curvature_hasDerivAt smooth reg u
    have hj := curvatureGradient_hasDerivAt smooth reg u
    have hp := cp.differentiable (by simp) u
    have hF : HasDerivAt F (g u*p u) u := hasDerivAt_speed_smul_arcDerivative reg (cF.differentiable (by simp)) u
    have hx : HasDerivAt h (g u*q u) u := by
      simpa only [h,Function.comp_def,map_smul,smul_eq_mul] using
        l.hasFDerivAt.comp_hasDerivAt u (position_hasDerivAt smooth reg u)
    have hq : HasDerivAt q (g u*k u*n u) u := by
      simpa only [q,g,k,n,Function.comp_def,←Complex.real_smul,map_smul,smul_eq_mul] using
        l.hasFDerivAt.comp_hasDerivAt u (tangent_hasDerivAt smooth reg u)
    have hw : HasDerivAt w (a u*(g u*q u)) u := (cf.differentiable (by simp) _).hasDerivAt.comp u hx
    have ha : HasDerivAt a (b u*(g u*q u)) u := (ca0.differentiable (by simp) _).hasDerivAt.comp u hx
    have der := (((hw.mul hk).neg.mul hp.hasDerivAt).add ((((ha.mul hq).mul hk).add (hw.mul hj)).mul hF))
    have dNeq : deriv (c.velocityGradientNormal t) u= -deriv p u := by
      rw [neqn]; exact hp.hasDerivAt.neg.deriv
    dsimp only [time,rate]
    rw [dNeq,(c.arcTurn_frameRate hf ht u).2,show deriv flux u=_ from der.deriv]
    dsimp only [F,k,j,g,x,force,Pi.add_apply,Pi.mul_apply,Pi.neg_apply]
    ring
  apply (c.projectedBendingMass_material hf l cf ht).congr_deriv
  change (∫ u in 0..c.period, time u) = ∫ u in 0..c.period, rate u
  calc
    _ = ∫ u in 0..c.period, rate u + deriv flux u :=
      intervalIntegral.integral_congr (fun u _ => point u)
    _ = _ := by rw [intervalIntegral.integral_add (crate.intervalIntegrable _ _)
      (hdflux.intervalIntegrable _ _),zero,add_zero]

end LengthGrowth.ActualFlow.SmoothPeriodicImmersion
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.projectedBendingMass_material
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.projectedBendingMass_flux
