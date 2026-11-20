import Migration.CurveKinematics

/-! First variation of the arclength mass of a fixed height cutoff. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def IsNormalFEF : Prop := ∀ t ∈ I, ∀ u,
  HasDerivAt (fun x => c.position x u) ((-force (c.position t) u) • normal (c.position t) u) t

theorem velocity_eq_normal (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    c.velocity t u = (-force (c.position t) u) • normal (c.position t) u :=
  (c.position_time_hasDerivAt ht u).unique (hflow t ht u)

theorem speed_normal_hasDerivAt (hflow : c.IsNormalFEF) {t : ℝ} (ht : t ∈ I) (u : ℝ) :
    HasDerivAt (fun v => speed (c.position v) u)
      (speed (c.position t) u * curvature (c.position t) u * force (c.position t) u) t := by
  have hg := c.speed_time_hasDerivAt ht u
  rw [c.speed_mul_velocityGradientTangent ht u] at hg
  have hzero : (fun v => inner ℝ (tangent (c.position t) v) (c.velocity t v)) = fun _ => 0 := by
    funext v
    rw [c.velocity_eq_normal hflow ht v, real_inner_smul_right, tangent_normal_orthogonal, mul_zero]
  have hd := (tangent_hasDerivAt (c.position_slice_smooth ht) (c.immersion t ht) u).inner ℝ
    ((c.velocity_slice_smooth ht).differentiable (by simp) u).hasDerivAt
  rw [hzero] at hd
  have he := hd.unique (hasDerivAt_const u (0:ℝ))
  rw [← Complex.real_smul, real_inner_smul_left, c.velocity_eq_normal hflow ht u,
    real_inner_smul_right, real_inner_self_eq_norm_sq, normal_unit (c.immersion t ht)] at he
  apply hg.congr_deriv
  rw [real_inner_comm]
  nlinarith

def cutoffMass (H : ℂ →L[ℝ] ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..c.period, p (H (c.position t u)) * speed (c.position t) u

def cutoffMassRate (H : ℂ →L[ℝ] ℝ) (p dp : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..c.period, (curvature (c.position t) u * p (H (c.position t u)) -
    dp (H (c.position t u)) * H (normal (c.position t) u)) *
    force (c.position t) u * speed (c.position t) u

theorem cutoffMass_hasDerivAt (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    (p dp : ℝ → ℝ) (hp : ∀ h, HasDerivAt p (dp h) h) (hdp : Continuous dp)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (c.cutoffMass H p) (c.cutoffMassRate H p dp t) t := by
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun h => (hp h).continuousAt
  have hh := H.continuous.comp_continuousOn c.joint_smooth.continuousOn
  have hN := H.continuous.comp_continuousOn c.normal_joint_smooth.continuousOn
  have hsub : I ×ˢ uIcc 0 c.period ⊆ I ×ˢ (univ : Set ℝ) := fun z hz => ⟨hz.1, mem_univ _⟩
  apply hasDerivAt_intervalIntegral_of_continuousOn (a := 0) (b := c.period)
    (F := fun v u => p (H (c.position v u))*speed (c.position v) u)
    (D := fun v u => (curvature (c.position v) u*p (H (c.position v u)) -
      dp (H (c.position v u))*H (normal (c.position v) u))*force (c.position v) u*
        speed (c.position v) u) c.time_open
  · exact ((hpc.comp_continuousOn hh).mul c.speed_joint_smooth.continuousOn).mono hsub
  · have hk := c.curvature_joint_smooth.continuousOn.mul (hpc.comp_continuousOn hh)
    have hd := (hdp.comp_continuousOn hh).mul hN
    exact (((hk.sub hd).mul c.force_joint_smooth.continuousOn).mul
      c.speed_joint_smooth.continuousOn).mono hsub
  · intro v hv u _
    have hh' := H.hasFDerivAt.comp_hasDerivAt v (hflow v hv u)
    have h := ((hp (H (c.position v u))).comp v hh').mul (c.speed_normal_hasDerivAt hflow hv u)
    apply h.congr_deriv
    simp only [map_smul, smul_eq_mul, Function.comp_apply]
    ring
  · exact ht

end MigrationGeometry.Flow.SmoothPeriodicImmersion
