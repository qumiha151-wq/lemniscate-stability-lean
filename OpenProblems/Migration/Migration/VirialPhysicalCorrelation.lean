import Migration.VirialMaterialCubic
import Migration.VirialForceProduct

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Cubic cancellation in the actual support/flux moment, in physical units. -/
theorem quarter_physical_correlation {t : ℝ} (ht : t∈I) (turn : c.signedCurvatureIntegral t=2*Real.pi)
    (small : c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2≤1/4) (e : ℂ) (he : ‖e‖=1) :
    |c.supportFluxCorrelation (innerSL ℝ e) t|≤c.coreLength t^2/(2*Real.pi)*
      (95/100*(c.curvatureOscillation (2*Real.pi) t/(2*Real.pi)^2)) := by
  let p:=c.materialSlice ht
  let B:=c.arclengthCentroid t
  let a:=2*Real.pi
  let u:=fun x=>p.arclengthInverse (p.length*x)
  let G:=p.fractionalPosition B
  let T:=p.fractionalTangent
  let K:=fun x=>p.fractionalCurvature x/a
  let N:=fun x=>Complex.I*T x
  let f:=fun y=>inner ℝ (normal p.position y) (p.position y-B)
  let Q:=fun y=>curvature p.position y*(inner ℝ e (p.position y)-c.centroidHeight (innerSL ℝ e) t)+inner ℝ e (normal p.position y)
  let Z:=fun x=>(inner ℝ (N x) (G x)) • ((K x:ℂ)*G x+N x)
  have ap : 0<a := by dsimp [a];positivity
  have lp:=p.length_pos
  have cf : Continuous f := (normal_smooth p.smooth p.regular).continuous.inner (p.smooth.continuous.sub continuous_const)
  have cq : Continuous Q := ((curvature_smooth p.smooth p.regular).continuous.mul
    (((innerSL ℝ e).continuous.comp p.smooth.continuous).sub continuous_const)).add
    ((innerSL ℝ e).continuous.comp (normal_smooth p.smooth p.regular).continuous)
  have cg : Continuous G := continuous_iff_continuousAt.mpr fun x=>(p.fractionalPosition_der B x).continuousAt
  have ct : Continuous T := continuous_iff_continuousAt.mpr fun x=>(p.fractionalTangent_hasDerivAt x).continuousAt
  have cn : Continuous N := continuous_const.mul ct
  have ck : Continuous K := (continuous_const.mul ((curvature_smooth p.smooth p.regular).continuous.comp
    (p.inverse_continuous.comp (continuous_const.mul continuous_id)))).div_const a
  have cp : Continuous (fun x=>inner ℝ (N x) (G x)) := cn.inner cg
  have cz : Continuous Z := cp.smul (((Complex.continuous_ofReal.comp ck).mul cg).add cn)
  have spatial (x : ℝ) : (innerSL ℝ e) (Z x)=(a/p.length)*(f (u x)*Q (u x)) := by
    have nz : N x=normal p.position (u x) := rfl
    have h0 : (K x:ℂ)*G x=curvature p.position (u x) • (p.position (u x)-B) := by
      change ((p.length*curvature p.position (u x)/a:ℝ):ℂ)*((a/p.length) • (p.position (u x)-B))=_
      rw [←Complex.real_smul,smul_smul,show p.length*curvature p.position (u x)/a*(a/p.length)=curvature p.position (u x) by field_simp]
    change inner ℝ e ((inner ℝ (N x) (G x)) • ((K x:ℂ)*G x+N x))=_
    rw [h0,nz,real_inner_smul_right,inner_add_right,real_inner_smul_right,inner_sub_right]
    change inner ℝ (normal p.position (u x)) ((a/p.length) • (p.position (u x)-B))*_ =_
    rw [real_inner_smul_right]
    have cen : inner ℝ e B=c.centroidHeight (innerSL ℝ e) t := c.map_arclengthCentroid (innerSL ℝ e) ht
    rw [cen];dsimp only [f,Q];ring
  let J:=∫x in (0:ℝ)..1,Z x
  have exactJ : inner ℝ e J=(a/p.length)*(∫x in (0:ℝ)..1,(f (u x)*Q (u x))) := by
    have H:=(innerSL ℝ e).intervalIntegral_comp_comm (μ:=volume) (a:=0) (b:=1) (cz.intervalIntegrable ..)
    change _ = inner ℝ e J at H
    rw [←H]
    change (∫x in (0:ℝ)..1,(innerSL ℝ e) (Z x))=_
    simp only [spatial,intervalIntegral.integral_const_mul]
  have convertJ:=p.fractional_integral_eq (cf.mul cq)
  change p.length*(∫x in (0:ℝ)..1,f (u x)*Q (u x))=c.supportFluxCorrelation (innerSL ℝ e) t at convertJ
  have eq : c.supportFluxCorrelation (innerSL ℝ e) t=(p.length^2/a)*(inner ℝ e J) := by
    rw [←convertJ,exactJ];field_simp
  have C:=c.quarter_support_flux_mean ht turn small
  change ‖J‖≤_ at C
  have cs:=abs_real_inner_le_norm e J
  rw [he,one_mul] at cs
  rw [eq,abs_mul,abs_of_nonneg (div_nonneg (sq_nonneg _) ap.le)]
  exact mul_le_mul_of_nonneg_left (cs.trans C) (div_nonneg (sq_nonneg _) ap.le)

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.quarter_physical_correlation

