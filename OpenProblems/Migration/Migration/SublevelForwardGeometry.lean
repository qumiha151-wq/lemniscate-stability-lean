import Migration.SublevelForwardHull
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

private theorem initial_integral_continuity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (f : ℝ→ℝ→V)
    (hf : ContinuousOn (fun q : ℝ×ℝ=>f q.1 q.2) (Ici 0×ˢuniv)) (p : ℝ) :
    ContinuousWithinAt (fun t=>∫u in 0..p,f t u) (Ici 0) 0 := by
  have cc : Continuous (fun q : ℝ×ℝ=>f (max q.1 0) q.2) :=
    hf.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun q=>⟨show 0≤max q.1 0 from le_max_right _ _,mem_univ _⟩)
  have ci := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ:=volume) (f:=fun t u=>f (max t 0) u) cc 0 p
  have onK : ContinuousOn (fun t=>∫u in 0..p,f t u) (Ici 0) := ci.continuousOn.congr
    (fun t ht=>by simp only [max_eq_left (show 0≤t from ht)])
  exact onK 0 (show (0:ℝ)≤0 from le_rfl)

/-- Classical one-sided initial data: the physical position, speed and curvature
are jointly continuous down to time zero, and the initial curve is immersed. -/
theorem classical_forward_initial_disk (hf : c.IsNormalFEF)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (regular : ∀u,deriv (c.position 0) u≠0)
    (initial : 2*c.bending 0*c.coreLength 0≤4*Real.pi^2+11/2)
    {t : ℝ} (ht : 0≤t) :
    Metric.closedBall (c.arclengthCentroid 0) ((85/100)*Real.pi/c.bending 0) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have en : ContinuousWithinAt c.bending (Ici 0) 0 :=
    (initial_integral_continuity (fun t u=>curvature (c.position t) u^2*speed (c.position t) u)
      ((curv.pow 2).mul spd) c.period).div_const _
  have len : ContinuousWithinAt c.coreLength (Ici 0) 0 :=
    initial_integral_continuity (fun t u=>speed (c.position t) u) spd c.period
  have mom := initial_integral_continuity (fun t u=>speed (c.position t) u • c.position t u)
      (spd.smul position) c.period
  have sc : Continuous (fun u=>speed (c.position 0) u) :=
    spd.comp_continuous (continuous_const.prodMk continuous_id) (fun _=>⟨by simp,mem_univ _⟩)
  have lp : 0<c.coreLength 0 := by
    apply intervalIntegral.integral_pos c.period_pos sc.continuousOn
    · exact fun u _=>(speed_pos regular u).le
    · exact ⟨0,⟨le_rfl,c.period_pos.le⟩,speed_pos regular 0⟩
  have cen : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0 :=
    (len.inv₀ lp.ne').smul mom
  have ev : ∀ᶠ v in 𝓝[>] (0:ℝ), c.bending 1≤c.bending v := by
    have small : ∀ᶠ v in 𝓝[>] (0:ℝ), v<1 := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin,small] with v (hv : 0<v) h1
    exact c.bending_le_of_slab hf Complex.reCLM h1.le (fun _ h=>lt_of_lt_of_le hv h.1)
  have ep := lt_of_lt_of_le (c.bending_pos_of_width (show (1:ℝ)∈Ioi 0 by norm_num))
    (le_of_tendsto_of_tendsto tendsto_const_nhds (en.mono Ioi_subset_Ici_self).tendsto ev)
  exact c.forward_all_hulls_common_disk hf position en len cen ep initial ht

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.classical_forward_initial_disk
