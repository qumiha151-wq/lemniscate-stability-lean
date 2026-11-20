import SolitonClassification.FrozenStressBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.FrozenStress

theorem scalar_segment_bound {f g : ℝ→ℝ} (dg : ∀x,HasDerivAt f (g x) x)
    {C s t : ℝ} (hs : 0≤s) (hst : s≤t) (bound : ∀x≥0,|g x|≤C) :
    |f t-f s|≤C*(t-s) := by
  exact norm_image_sub_le_of_norm_deriv_le_segment' (fun x _ => (dg x).hasDerivWithinAt)
    (fun x hx => bound x (hs.trans hx.1)) t ⟨hst,le_rfl⟩

/-- A converging real-valued function with uniformly Lipschitz derivative
on the positive half line has derivative tending to zero. -/
theorem derivative_vanishes_on_tail {f g j : ℝ→ℝ} {C L : ℝ}
    (df : ∀x,HasDerivAt f (g x) x) (dg : ∀x,HasDerivAt g (j x) x)
    (bound : ∀x≥0, |j x|≤C) (fl : Tendsto f atTop (𝓝 L)) :
    Tendsto g atTop (𝓝 0) := by
  have cn : 0≤C := (abs_nonneg _).trans (bound 0 le_rfl)
  apply Metric.tendsto_nhds.mpr
  intro ε ep
  let d := ε/(4*(C+1))
  have dp : 0<d := by dsimp [d]; positivity
  have small : C*d≤ε/4 := by
    have eq : (C+1)*d=ε/4 := by dsimp [d]; field_simp
    linarith only [eq,dp]
  have slide : Tendsto (fun x : ℝ => x+d) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
  have sec : Tendsto (fun x => (f (x+d)-f x)/d) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,sub_self,zero_div] using ((fl.comp slide).sub fl).div_const d
  filter_upwards [(Metric.tendsto_nhds.mp sec) (ε/2) (by positivity),eventually_ge_atTop (0:ℝ)] with t hs ht
  have cf : Continuous f := continuous_iff_continuousAt.mpr fun _ => (df _).continuousAt
  obtain ⟨y,hy,eq⟩ := exists_hasDerivAt_eq_slope f g (a:=t) (b:=t+d) (by linarith)
    cf.continuousOn (fun x _ => df x)
  rw [add_sub_cancel_left] at eq
  have slope := scalar_segment_bound dg ht hy.1.le bound
  have gap := mul_le_mul_of_nonneg_left (show y-t≤d by linarith [hy.2]) cn
  change dist ((f (t+d)-f t)/d) 0<ε/2 at hs
  rw [Real.dist_eq,sub_zero] at hs ⊢
  rw [←eq] at hs
  have tri := abs_add_le (g t-g y) (g y)
  rw [sub_add_cancel,abs_sub_comm] at tri
  linarith

end ClosedSimilarity.FrozenStress
#print axioms ClosedSimilarity.FrozenStress.derivative_vanishes_on_tail
