import Migration.LocalizedRateBound
import Migration.LocalizedLengthCost

/-! A finite-time cost for changing an actual closed curve's weighted length. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem cutoffMassRate_continuousOn (H : ℂ →L[ℝ] ℝ) {p dp : ℝ → ℝ}
    (hp : Continuous p) (hd : Continuous dp) :
    ContinuousOn (c.cutoffMassRate H p dp) I := by
  have hh := H.continuous.comp_continuousOn c.joint_smooth.continuousOn
  have hN := H.continuous.comp_continuousOn c.normal_joint_smooth.continuousOn
  have hk := c.curvature_joint_smooth.continuousOn.mul (hp.comp_continuousOn hh)
  have hb := (hd.comp_continuousOn hh).mul hN
  apply continuousOn_intervalIntegral_of_isOpen (a := 0) (b := c.period)
    (F := fun v u => (curvature (c.position v) u*p (H (c.position v u)) -
      dp (H (c.position v u))*H (normal (c.position v) u))*force (c.position v) u*
        speed (c.position v) u) c.time_open
  exact (((hk.sub hb).mul c.force_joint_smooth.continuousOn).mul c.speed_joint_smooth.continuousOn).mono
    (fun _ hz => ⟨hz.1,mem_univ _⟩)

theorem localDissipation_continuousOn (H : ℂ →L[ℝ] ℝ) {r : ℝ → ℝ} (hr : Continuous r) :
    ContinuousOn (c.localDissipation H r) I := by
  have hh := H.continuous.comp_continuousOn c.joint_smooth.continuousOn
  apply continuousOn_intervalIntegral_of_isOpen (a := 0) (b := c.period)
    (F := fun v u => (r (H (c.position v u))*force (c.position v) u)^2 * speed (c.position v) u)
    c.time_open
  exact ((((hr.comp_continuousOn hh).mul c.force_joint_smooth.continuousOn).pow 2).mul
    c.speed_joint_smooth.continuousOn).mono (fun _ hz => ⟨hz.1,mem_univ _⟩)

/-- On an actual normal FEF, transit between zero mass and mass at least W
costs local dissipation. The stated bending ceiling and endpoint mass tests
concern the given position family. -/
theorem actual_cutoff_transit_cost (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    {p dp r : ℝ → ℝ} (hp' : ∀ h, HasDerivAt p (dp h) h)
    (hdc : Continuous dp) (hrc : Continuous r) {A B W T : ℝ}
    (hA : 0 ≤ A) (hB : 0 < B) (hW : 0 ≤ W) (hT : 0 < T)
    (hp : ∀ z, 0 ≤ p z) (hp1 : ∀ z, p z ≤ 1)
    (hd : ∀ z, |dp z| ≤ A*Real.sqrt (p z)) (hr : ∀ z, p z ≠ 0 → r z=1)
    (hslab : Icc 0 T ⊆ I) (henergy : ∀ t ∈ Icc 0 T, 2*c.bending t ≤ B^2)
    (hend : (W ≤ c.cutoffMass H p 0 ∧ c.cutoffMass H p T = 0) ∨
      (c.cutoffMass H p 0 = 0 ∧ W ≤ c.cutoffMass H p T)) :
    (W / (B+A*Real.sqrt W))^2 ≤ T * ∫ t in 0..T, c.localDissipation H r t := by
  have hpc := continuous_iff_continuousAt.mpr (fun h => (hp' h).continuousAt)
  apply MigrationGeometry.cutoffMass_transit_cost hA hB hW hT (c.cutoffMass H p)
    (c.cutoffMassRate H p dp) (c.localDissipation H r)
  · intro t ht
    exact (c.cutoffMass_hasDerivAt hflow H p dp hp' hdc (hslab ht)).continuousAt.continuousWithinAt
  · exact (c.cutoffMassRate_continuousOn H hpc hdc).mono hslab
  · intro t ht
    exact c.cutoffMass_hasDerivAt hflow H p dp hp' hdc (hslab ⟨ht.1.le,ht.2.le⟩)
  · exact ((c.localDissipation_continuousOn H hrc).mono hslab).intervalIntegrable_of_Icc hT.le
  · intro t ht
    have h := c.cutoffMassRate_bound H hH p dp r hpc hdc hrc hA hp hp1 hd hr (hslab ht)
    have hroot := (Real.sqrt_le_left hB.le).mpr (henergy t ht)
    have h' := h.trans (mul_le_mul_of_nonneg_right (add_le_add hroot le_rfl) (Real.sqrt_nonneg _))
    have hD : 0 ≤ c.localDissipation H r t :=
      intervalIntegral.integral_nonneg_of_forall c.period_pos.le
        (fun u => mul_nonneg (sq_nonneg _) (speed_pos (c.immersion t (hslab ht)) u).le)
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hD] using pow_le_pow_left₀ (abs_nonneg _) h' 2
  · exact hend

end MigrationGeometry.Flow.SmoothPeriodicImmersion
