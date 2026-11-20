import LengthGrowth.ActualFlow.GrowthEquivalence

/-! Signed total curvature is constant along smooth regular homotopies.
If the curvature eventually has one sign in space, total absolute curvature
is bounded globally, giving the fourth-root length and energy bounds. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace LengthGrowth.ActualFlow

def materialSignedCurvature (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ u in 0..P, curvature γ u * speed γ u

namespace SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem signedCurvature_hasDerivAt_zero {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun x => materialSignedCurvature (c.position x) c.period) 0 t := by
  have h := hasDerivAt_intervalIntegral_of_jointC1 (a := 0) (b := c.period)
    (F := fun t u => curvature (c.position t) u * speed (c.position t) u)
    c.time_open ((c.curvature_joint_smooth.mul c.speed_joint_smooth).of_le (by simp)) ht
  have hi : (∫ u in 0..c.period, deriv (fun x =>
      curvature (c.position x) u * speed (c.position x) u) t) =
      ∫ u in 0..c.period, deriv (c.velocityGradientNormal t) u := by
    apply intervalIntegral.integral_congr
    intro u _
    have hk := joint_smooth_time_hasDerivAt c.time_open
      (f := fun x => curvature (c.position x)) c.curvature_joint_smooth ht u
    have hg := joint_smooth_time_hasDerivAt c.time_open
      (f := fun x => speed (c.position x)) c.speed_joint_smooth ht u
    calc
      _ = _ := (hk.mul hg).deriv
      _ = _ := by linarith only [c.curvature_metric_time_identity ht u]
  have hb := joint_smooth_space_slice (f := c.velocityGradientNormal)
    c.velocityGradientNormal_joint_smooth ht
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c.period)
    (fun u _ => (hb.differentiable (by simp) u).hasDerivAt)
    ((contDiff_infty_iff_deriv.mp hb).2.continuous.intervalIntegrable _ _)
  have hp : c.velocityGradientNormal t c.period = c.velocityGradientNormal t 0 := by
    simpa using c.velocityGradientNormal_periodic ht 0
  rw [hi, hft, hp, sub_self] at h
  exact h
end SmoothPeriodicImmersion

namespace ForwardImmersion
variable (c : ForwardImmersion)

theorem signedCurvature_continuousOn : ContinuousOn
    (fun t => materialSignedCurvature (c.position t) c.period) (Ici 0) :=
  continuousOn_intervalIntegral_forward
    ((c.curvature_continuousOn.mul c.speed_continuousOn).mono
      (fun _ hz => ⟨hz.1, mem_univ _⟩))

theorem signedCurvature_eq_initial {t : ℝ} (ht : 0 ≤ t) :
    materialSignedCurvature (c.position t) c.period =
      materialSignedCurvature (c.position 0) c.period := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (c.signedCurvature_continuousOn.mono (fun _ hx => hx.1))
    (fun x hx => c.interior.signedCurvature_hasDerivAt_zero hx.1)
    (intervalIntegrable_const (c := (0 : ℝ)))
  simpa using (sub_eq_zero.mp (by simpa using h.symm))

theorem absoluteCurvature_continuousOn : ContinuousOn c.absoluteCurvature (Ici 0) :=
  continuousOn_intervalIntegral_forward
    ((c.curvature_continuousOn.abs.mul c.speed_continuousOn).mono
      (fun _ hz => ⟨hz.1, mem_univ _⟩))

/-- The sign is allowed to be chosen separately at every late time. -/
theorem bounded_absoluteCurvature_of_eventual_spatial_sign {T : ℝ} (hT : 0 ≤ T)
    (hsg : ∀ t, T ≤ t → (∀ u, 0 ≤ curvature (c.position t) u) ∨
      (∀ u, curvature (c.position t) u ≤ 0)) : c.HasBoundedAbsoluteCurvature := by
  obtain ⟨x, _, hx⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
    (c.absoluteCurvature_continuousOn.mono (fun _ h => h.1))
  refine ⟨max (c.absoluteCurvature x) |materialSignedCurvature (c.position 0) c.period|, ?_⟩
  intro t ht
  by_cases h : t ≤ T
  · exact (hx ⟨ht, h⟩).trans (le_max_left ..)
  apply le_trans _ (le_max_right ..)
  rw [← c.signedCurvature_eq_initial ht]
  rcases hsg t (le_of_not_ge h) with hp | hn
  · have hh : c.absoluteCurvature t = materialSignedCurvature (c.position t) c.period := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [abs_of_nonneg (hp u)]
    exact hh.le.trans (le_abs_self _)
  · have hh : c.absoluteCurvature t = -materialSignedCurvature (c.position t) c.period := by
      rw [materialSignedCurvature, ← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [abs_of_nonpos (hn u), neg_mul]
    exact hh.le.trans (neg_le_abs _)

theorem quarter_bounds_of_eventual_spatial_curvature_sign (hf : c.IsNormalFEF) {T : ℝ}
    (hT : 0 ≤ T) (hsg : ∀ t, T ≤ t → (∀ u, 0 ≤ curvature (c.position t) u) ∨
      (∀ u, curvature (c.position t) u ≤ 0)) :
    c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound := by
  have hl := c.quarter_length_of_bounded_absoluteCurvature hf
    (c.bounded_absoluteCurvature_of_eventual_spatial_sign hT hsg)
  exact ⟨hl, c.quarter_energy_of_quarter_length hf hl⟩
end ForwardImmersion
end LengthGrowth.ActualFlow

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_bounds_of_eventual_spatial_curvature_sign
