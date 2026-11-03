import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A two-point bound for the quadratic remainder of a C2 map.
The proof uses the existing local Lipschitz theorem for C1 maps and the
convex-set mean value inequality with a fixed linear term subtracted.
-/
noncomputable section
namespace Lemniscate
open Set Filter
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The nonlinear remainder of a C2 map is locally Lipschitz with a factor
linear in the sizes of both arguments. No completeness hypothesis is needed. -/
theorem exists_local_quadratic_remainder_lipschitz {G : E → F}
    (hG : ContDiffAt ℝ 2 G 0) :
    ∃ δ > 0, ∃ C > 0, ∀ u ∈ Metric.ball (0:E) δ, ∀ v ∈ Metric.ball (0:E) δ,
      ‖G u-G v-(fderiv ℝ G 0) (u-v)‖ ≤ C*(‖u‖+‖v‖)*‖u-v‖ := by
  obtain ⟨D,⟨s,hs,hD⟩,hDcont⟩ :=
    (contDiffAt_succ_iff_hasFDerivAt (n := 1)).mp hG
  obtain ⟨L,t,ht,hLip⟩ := hDcont.exists_lipschitzOnWith
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hs ht)
  have hzero : (0:E) ∈ Metric.ball (0:E) δ := Metric.mem_ball_self hδ
  have hDzero : fderiv ℝ G 0 = D 0 := (hD 0 (hball hzero).1).fderiv
  refine ⟨δ,hδ,(L:ℝ)+1,add_pos_of_nonneg_of_pos L.coe_nonneg zero_lt_one,?_⟩
  intro u hu v hv
  let R : ℝ := max ‖u‖ ‖v‖
  have hu' : ‖u‖ < δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hu
  have hv' : ‖v‖ < δ := by
    simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hv
  have hR : R < δ := max_lt hu' hv'
  have hsub : Metric.closedBall (0:E) R ⊆ Metric.ball (0:E) δ :=
    Metric.closedBall_subset_ball hR
  have huR : u ∈ Metric.closedBall (0:E) R := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero] using
      (le_max_left ‖u‖ ‖v‖)
  have hvR : v ∈ Metric.closedBall (0:E) R := by
    simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero] using
      (le_max_right ‖u‖ ‖v‖)
  have hRsum : R ≤ ‖u‖+‖v‖ :=
    max_le (le_add_of_nonneg_right (norm_nonneg v))
      (le_add_of_nonneg_left (norm_nonneg u))
  have hbound : ∀ w ∈ Metric.closedBall (0:E) R,
      ‖D w-D 0‖ ≤ ((L:ℝ)+1)*(‖u‖+‖v‖) := by
    intro w hw
    have hw' : ‖w‖ ≤ R := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero] using hw
    have hLipw : ‖D w-D 0‖ ≤ (L:ℝ)*‖w‖ := by
      simpa only [dist_eq_norm,sub_zero] using
        hLip.dist_le_mul w (hball (hsub hw)).2 0 (hball hzero).2
    calc
      ‖D w-D 0‖ ≤ (L:ℝ)*‖w‖ := hLipw
      _ ≤ (L:ℝ)*(‖u‖+‖v‖) :=
        mul_le_mul_of_nonneg_left (hw'.trans hRsum) L.coe_nonneg
      _ ≤ ((L:ℝ)+1)*(‖u‖+‖v‖) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (add_nonneg (norm_nonneg u) (norm_nonneg v))
  have hmean :=
    (convex_closedBall (0:E) R).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := G) (f' := D) (φ := D 0)
      (fun w hw => (hD w (hball (hsub hw)).1).hasFDerivWithinAt)
      hbound hvR huR
  simpa only [hDzero] using hmean

end Lemniscate
