import Migration.BendingVariation

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem bending_nonneg (t : ℝ) : 0 ≤ c.bending t := by
  unfold bending
  apply div_nonneg _ (by norm_num)
  exact intervalIntegral.integral_nonneg_of_forall c.period_pos.le
    (fun u => mul_nonneg (sq_nonneg _) (norm_nonneg _))

theorem bending_hasDerivAt_dissipation (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt c.bending (-c.localDissipation H (fun _ => 1) t) t := by
  have hb : c.bending = c.energy := by
    funext x
    unfold bending energy
    ring
  rw [hb]
  apply (c.energy_hasDerivAt_firstVariation ht).congr_deriv
  unfold localDissipation
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [c.velocity_eq_normal hflow ht u, real_inner_smul_right, real_inner_self_eq_norm_sq,
    normal_unit (c.immersion t ht)]
  ring

theorem full_dissipation_eq_bending_drop (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    {s t : ℝ} (hst : s ≤ t) (hslab : Icc s t ⊆ I) :
    (∫ v in s..t, c.localDissipation H (fun _ => 1) v) = c.bending s-c.bending t := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (f := c.bending) (f' := fun v => -c.localDissipation H (fun _ => 1) v)
    (fun v hv => (c.bending_hasDerivAt_dissipation hflow H (hslab hv)).continuousAt.continuousWithinAt)
    (fun v hv => c.bending_hasDerivAt_dissipation hflow H (hslab ⟨hv.1.le,hv.2.le⟩))
    ((((c.localDissipation_continuousOn H continuous_const).mono hslab).neg).intervalIntegrable_of_Icc hst
    )
  rw [intervalIntegral.integral_neg] at hi
  linarith

theorem bending_le_of_slab (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    {s t : ℝ} (hst : s ≤ t) (hslab : Icc s t ⊆ I) : c.bending t ≤ c.bending s := by
  have hi := c.full_dissipation_eq_bending_drop hflow H hst hslab
  have hd : 0 ≤ ∫ v in s..t, c.localDissipation H (fun _ => 1) v :=
    intervalIntegral.integral_nonneg_of_forall hst (fun v =>
      intervalIntegral.integral_nonneg_of_forall c.period_pos.le
        (fun u => mul_nonneg (sq_nonneg _) (norm_nonneg _)))
  linarith

end MigrationGeometry.Flow.SmoothPeriodicImmersion
