import LengthGrowth.ActualFlow.MaterialTurnPrimitives
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

private theorem max_sign {f k v : ℝ→ℝ} (h : ∀y,HasDerivAt f (k y*v y) y)
    (vk : ∀y,0<v y) (ck : Continuous k) (cd : Continuous (deriv k))
    {x : ℝ} (mx : IsLocalMax f x) : k x=0 ∧ deriv k x≤0 := by
  have zero := (mul_eq_zero.mp (mx.hasDerivAt_eq_zero (h x))).resolve_right (vk x).ne'
  refine ⟨zero,?_⟩
  by_contra! pos
  have positive : ∀ᶠ y in 𝓝 x, 0<deriv k y := cd.continuousAt (Ioi_mem_nhds pos)
  have near : ∀ᶠ y in 𝓝 x, 0<deriv k y ∧ f y≤f x := Filter.Eventually.and positive mx
  obtain ⟨r,rp,small⟩ := Metric.eventually_nhds_iff.mp near
  let b := x+r/2
  have xb : x<b := by dsimp [b]; linarith
  have close {y : ℝ} (hy : y∈Icc x b) : dist y x<r := by
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hy.1)]
    dsimp [b] at hy
    linarith only [hy.2,rp]
  have grow : StrictMonoOn k (Icc x b) := strictMonoOn_of_deriv_pos (convex_Icc ..) ck.continuousOn
    (fun y hy => (small (close (interior_subset hy))).1)
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun y => (h y).continuousAt
  have gf : StrictMonoOn f (Icc x b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc ..) cf.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(h y).deriv]
    apply mul_pos _ (vk y)
    rw [←zero]
    exact grow (left_mem_Icc.mpr xb.le) ⟨hy.1.le,hy.2.le⟩ hy.1
  exact (not_lt_of_ge (small (close (right_mem_Icc.mpr xb.le))).2)
    (gf (left_mem_Icc.mpr xb.le) (right_mem_Icc.mpr xb.le) xb)

private theorem angular_derivative (p : PeriodicRegularPosition) (u : ℝ) :
    HasDerivAt (arcTurn p.position 0) (curvature p.position u*speed p.position u) u := by
  have hc := (curvature_smooth p.smooth p.regular).continuous.mul (speed_smooth p.smooth p.regular).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem max_inflection_sign (p : PeriodicRegularPosition) {u : ℝ} (h : IsLocalMax (arcTurn p.position 0) u) :
    curvature p.position u=0 ∧ curvatureGradient p.position u≤0 := by
  have c := curvature_smooth p.smooth p.regular
  obtain ⟨root,sign⟩ := max_sign p.angular_derivative (speed_pos p.regular) c.continuous
    (contDiff_infty_iff_deriv.mp c).2.continuous h
  exact ⟨root,mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (speed_pos p.regular u).le) sign⟩

set_option backward.isDefEq.respectTransparency false in
theorem min_inflection_sign (p : PeriodicRegularPosition) {u : ℝ} (h : IsLocalMin (arcTurn p.position 0) u) :
    curvature p.position u=0 ∧ 0≤curvatureGradient p.position u := by
  have c := curvature_smooth p.smooth p.regular
  have dg : deriv (fun y=> -curvature p.position y)=fun y=> -deriv (curvature p.position) y :=
    funext fun y => deriv.neg
  have cd : Continuous (deriv (fun y=> -curvature p.position y)) := by
    rw [dg]; exact (contDiff_infty_iff_deriv.mp c).2.continuous.neg
  have ds (y : ℝ) : HasDerivAt (-(arcTurn p.position 0)) ((-curvature p.position y)*speed p.position y) y := by
    rw [neg_mul]
    exact (p.angular_derivative y).neg
  obtain ⟨root,sign⟩ := max_sign (f:=-(arcTurn p.position 0)) (k:=fun y=> -curvature p.position y)
    ds (speed_pos p.regular) c.continuous.neg cd h.neg
  rw [dg] at sign
  exact ⟨neg_eq_zero.mp root,mul_nonneg (inv_nonneg.mpr (speed_pos p.regular u).le) (neg_nonpos.mp sign)⟩

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.max_inflection_sign
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.min_inflection_sign
