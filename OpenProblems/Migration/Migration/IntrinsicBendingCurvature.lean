import Migration.IntrinsicBendingDisk

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p:PeriodicRegularPosition)

theorem localBendingBound_of_curvature {M:ℝ} (hp:0<M)
    (h:∀u,|curvature p.position u|≤M) : p.localBendingBound (1/M) := by
  intro a
  have hn:0≤1/M:=(one_div_pos.mpr hp).le
  have k:=p.kAt_cont a
  have mono:=intervalIntegral.integral_mono_on (μ:=volume) hn ((k.pow 2).intervalIntegrable ..)
    (intervalIntegrable_const (c:=M^2)) (fun s _ => by
      change (curvature p.position (p.label a s))^2≤M^2
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (h (p.label a s)) 2)
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at mono
  have scaled:=mul_le_mul_of_nonneg_left mono hn
  change (1/M)*(∫s in (0:ℝ)..1/M,(p.kAt a s)^2)≤1
  exact scaled.trans_eq (by field_simp)

/-- A true curvature bound and small displacement of the image suffice even when
self-intersections or many passages occur in the same physical ball. -/
theorem disk_of_curvature_and_displacement {M:ℝ} (hp:0<M) (h:∀u,|curvature p.position u|≤M) :
    ∃z:ℂ, ∀B:Set ℂ,
      (∀u∈Icc 0 p.period, ∃y∈B, ‖p.position u-y‖≤(1/M)/24) →
      Metric.closedBall z ((1/M)/12)⊆convexHull ℝ B :=
  p.disk_of_intrinsic_scale (one_div_pos.mpr hp) (p.localBendingBound_of_curvature hp h)

end MigrationGeometry.Flow.PeriodicRegularPosition

#print axioms MigrationGeometry.Flow.PeriodicRegularPosition.disk_of_curvature_and_displacement
