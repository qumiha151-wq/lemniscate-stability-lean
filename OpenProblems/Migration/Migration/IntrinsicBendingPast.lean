import Migration.IntrinsicBendingCurvature
import Migration.BendingDissipation

noncomputable section
open Set
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- Integrate a lower bound on physical energy dissipation *before* the first of
two photographs. Both bending and dissipation are those of the given immersion. -/
theorem prior_energy_cost_of_dissipation_floor (hf : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    {a s t b : ℝ} (has : a ≤ s) (hst : s < t) (slab : Icc a s ⊆ I)
    (floor : ∀ v ∈ Icc a s, b/2*(t-v)^(-(3/2:ℝ)) ≤
      2*c.bending v*c.localDissipation H (fun _ => 1) v) :
    b*((t-s)^(-(1/2:ℝ))-(t-a)^(-(1/2:ℝ))) ≤ c.bending a^2-c.bending s^2 := by
  let Q := fun v : ℝ => c.bending v ^ 2 + b * (t-v)^(-(1/2:ℝ))
  have d (v : ℝ) (hv : v ∈ Icc a s) : HasDerivAt Q
      (-(2*c.bending v*c.localDissipation H (fun _=>1) v)+b/2*(t-v)^(-(3/2:ℝ))) v := by
    have ne : t-v ≠ 0 := (sub_pos.mpr (hv.2.trans_lt hst)).ne'
    have pow := ((hasDerivAt_id v).const_sub t).rpow_const (p:=-(1/2:ℝ)) (Or.inl ne)
    apply (((c.bending_hasDerivAt_dissipation hf H (slab hv)).pow 2).add (pow.const_mul b)).congr_deriv
    dsimp
    norm_num
    ring
  have mono : AntitoneOn Q (Icc a s) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a s)
    · exact fun v hv => (d v hv).continuousAt.continuousWithinAt
    · exact fun v hv => (d v (interior_subset hv)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [(d v (interior_subset hv)).deriv]
      linarith only [floor v (interior_subset hv)]
  have he := mono (show a ∈ Icc a s from ⟨le_rfl,has⟩) (show s ∈ Icc a s from ⟨has,le_rfl⟩) has
  dsimp [Q] at he
  linarith

end MigrationGeometry.Flow.SmoothPeriodicImmersion

#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.prior_energy_cost_of_dissipation_floor
