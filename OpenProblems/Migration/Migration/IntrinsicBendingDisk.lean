import Migration.IntrinsicBendingWidth

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.PeriodicRegularPosition
variable (p:PeriodicRegularPosition)

/-- One center works for every later image that approximates the initial image
on its full parameter period. The comparison allows arbitrary reparametrization. -/
theorem disk_of_intrinsic_scale {r:ℝ} (rp:0<r) (h:p.localBendingBound r) :
    ∃z:ℂ, ∀B:Set ℂ,
      (∀u∈Icc 0 p.period, ∃y∈B, ‖p.position u-y‖≤r/24) →
      Metric.closedBall z (r/12)⊆convexHull ℝ B := by
  let A:=p.position '' Icc 0 p.period
  have compact : IsCompact A:=isCompact_Icc.image p.smooth.continuous
  obtain ⟨z,center⟩:=exists_center_of_uniform_width compact (show 0<r/2 by positivity)
    (p.width_of_local_bending rp h)
  refine ⟨z,?_⟩
  intro B near x hx
  apply mem_convexHull_of_surrounding_directions
  intro e he
  obtain ⟨_,⟨u,hu,rfl⟩,margin⟩:=center e he
  obtain ⟨y,hy,close⟩:=near u hu
  have dx : ‖x-z‖≤r/12 := by simpa [Metric.mem_closedBall,dist_eq_norm] using hx
  have estimate (v w:ℂ) : inner ℝ e v-inner ℝ e w≤‖v-w‖ := by
    rw [←inner_sub_right]
    have b:=real_inner_le_norm e (v-w)
    rwa [he,one_mul] at b
  refine ⟨y,hy,?_⟩
  linarith only [rp,margin,(estimate x z).trans dx,(estimate (p.position u) y).trans close]

end MigrationGeometry.Flow.PeriodicRegularPosition

#print axioms MigrationGeometry.Flow.PeriodicRegularPosition.disk_of_intrinsic_scale
