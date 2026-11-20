import Migration.NearRoundCore
import Migration.NearRoundConvexDisk

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- A single center in physical coordinates and the instantaneous radius
`L(t)/(2S)`, expressed directly as a convex hull inclusion. -/
theorem fixed_centroid_ball_subset_convexHull (hf : c.IsNormalFEF)
    {s t S : ℝ} (hst : s ≤ t) (hslab : Icc s t ⊆ I) (hS : 2 ≤ S)
    (hm : ∀ v ∈ Icc s t, c.signedCurvatureIntegral v = S)
    (ho : ∀ v ∈ Icc s t, c.curvatureOscillation S v ≤ 1/64) :
    Metric.closedBall (c.arclengthCentroid s) (c.coreLength t/(2*S)) ⊆
      convexHull ℝ (c.position t '' Icc 0 c.period) := by
  have hSp : 0 < S := by linarith
  have hL := c.coreLength_pos (hslab ⟨hst,le_rfl⟩)
  apply closedBall_subset_convexHull_of_directional_margin (R := 9*c.coreLength t/(16*S))
  · apply (div_lt_div_iff₀ (mul_pos (by norm_num) hSp) (mul_pos (by norm_num) hSp)).mpr
    nlinarith [mul_pos hL hSp]
  · intro e he
    obtain ⟨u,hu,h⟩ := c.fixed_initial_centroid_support hf hst hslab hS hm ho e he
    exact ⟨c.position t u,⟨u,hu,rfl⟩,h⟩

/-- A single physical disk works simultaneously at every time on the slab. -/
theorem fixed_physical_ball_all_times (hf : c.IsNormalFEF)
    {s t S : ℝ} (hst : s ≤ t) (hslab : Icc s t ⊆ I) (hS : 2 ≤ S)
    (hm : ∀ v ∈ Icc s t, c.signedCurvatureIntegral v = S)
    (ho : ∀ v ∈ Icc s t, c.curvatureOscillation S v ≤ 1/64) :
    ∀ v ∈ Icc s t, Metric.closedBall (c.arclengthCentroid s) (S/(4*c.bending s)) ⊆
      convexHull ℝ (c.position v '' Icc 0 c.period) := by
  intro v hv
  have hs : s ∈ Icc s t := ⟨le_rfl,hst⟩
  have hsub : Icc s v ⊆ Icc s t := Icc_subset_Icc le_rfl hv.2
  have hSp : 0 < S := by linarith
  have hE : 0 < c.bending s := by
    have hiden := c.oscillation_energy_identity (hslab hs) (hm s hs)
    have hp := c.curvatureOscillation_nonneg (hslab hs) S
    by_contra! h
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h (c.coreLength_pos (hslab hs)).le, sq_pos_of_pos hSp]
  have hmono := c.bending_le_of_slab hf Complex.reCLM hv.1 (hsub.trans hslab)
  have hiden := c.oscillation_energy_identity (hslab hv) (hm v hv)
  have hpos := c.curvatureOscillation_nonneg (hslab hv) S
  have hr : S/(4*c.bending s) ≤ c.coreLength v/(2*S) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hE) (mul_pos (by norm_num) hSp)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hmono (c.coreLength_pos (hslab hv)).le]
  exact (Metric.closedBall_subset_closedBall hr).trans
    (c.fixed_centroid_ball_subset_convexHull hf hv.1 (hsub.trans hslab) hS
      (fun x hx => hm x (hsub hx)) (fun x hx => ho x (hsub hx)))

#print axioms fixed_centroid_ball_subset_convexHull
#print axioms fixed_physical_ball_all_times
end MigrationGeometry.Flow.SmoothPeriodicImmersion
