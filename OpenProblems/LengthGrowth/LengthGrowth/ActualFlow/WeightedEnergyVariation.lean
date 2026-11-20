import LengthGrowth.ActualFlow.WeightedForceRate

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Exponentially weighted bending energy plus the weighted length term,
in the original material coordinate. -/
def materialExponentialMass (l : ℂ →L[ℝ] ℝ) (a t : ℝ) : ℝ :=
  ∫ u in 0..c.period, Real.exp (a*l (c.position t u))*
    (curvature (c.position t) u^2/2+a^2)*speed (c.position t) u

/-- The genuine material first variation, before the two integrations by parts
in space. The first term uses the actual normal elastic velocity. -/
theorem materialExponentialMass_hasDerivAt (hf : c.IsNormalFEF) (l : ℂ →L[ℝ] ℝ)
    (a : ℝ) {t : ℝ} (ht : t∈I) : HasDerivAt (c.materialExponentialMass l a)
    (∫ u in 0..c.period, Real.exp (a*l (c.position t u))*
      (-a*l (normal (c.position t) u)*force (c.position t) u*
         (curvature (c.position t) u^2/2+a^2)*speed (c.position t) u+
       curvature (c.position t) u*deriv (c.velocityGradientNormal t) u+
       (a^2-curvature (c.position t) u^2/2)*
         (speed (c.position t) u*c.velocityGradientTangent t u))) t := by
  let w := fun t u => Real.exp (a*l (c.position t u))
  let k := fun t u => curvature (c.position t) u
  let g := fun t u => speed (c.position t) u
  have wl : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => l (c.position z.1 z.2)) (I ×ˢ univ) :=
    l.contDiff.comp_contDiffOn c.joint_smooth
  have ws : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ => w z.1 z.2) (I ×ˢ univ) :=
    (contDiffOn_const.mul wl).exp
  have ks := c.curvature_joint_smooth
  have gs := c.speed_joint_smooth
  have sm : ContDiffOn ℝ ∞ (fun z : ℝ×ℝ =>
      w z.1 z.2*(k z.1 z.2^2/2+a^2)*g z.1 z.2) (I ×ˢ univ) :=
    (ws.mul (((ks.pow 2).div_const 2).add contDiffOn_const)).mul gs
  have h := hasDerivAt_intervalIntegral_of_jointC1 (a:=0) (b:=c.period)
    (F:=fun t u => w t u*(k t u^2/2+a^2)*g t u) c.time_open (sm.of_le (by simp)) ht
  apply h.congr_deriv
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have hd := l.hasFDerivAt.comp_hasDerivAt t (hf t ht u)
  have hh : HasDerivAt (fun x => l (c.position x u)) (-force (c.position t) u*l (normal (c.position t) u)) t := by
    simpa only [Function.comp_def, ← Complex.ofReal_neg, ← Complex.real_smul,
      map_smul,smul_eq_mul] using hd
  have hw := (hh.const_mul a).exp
  have hk := joint_smooth_time_hasDerivAt c.time_open (f:=k) ks ht u
  have hg := c.speed_time_hasDerivAt ht u
  have ht' := (hw.mul (((hk.pow 2).div_const 2).add_const (a^2))).mul hg
  change deriv (fun x => w x u*(k x u^2/2+a^2)*g x u) t = _
  rw [show deriv (fun x => w x u*(k x u^2/2+a^2)*g x u) t = _ from ht'.deriv]
  dsimp [k,g,w]
  have metric := c.curvature_metric_rate_identity ht u
  linear_combination (Real.exp (a*l (c.position t u))*curvature (c.position t) u)*metric

end LengthGrowth.ActualFlow.SmoothPeriodicImmersion
#print axioms LengthGrowth.ActualFlow.SmoothPeriodicImmersion.materialExponentialMass_hasDerivAt
