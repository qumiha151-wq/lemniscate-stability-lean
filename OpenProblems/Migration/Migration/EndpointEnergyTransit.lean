import Migration.EndpointWidthTransit
import Migration.DirectionalWidth

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem pair_from_energy {t : ℝ} (ht : t∈I) (e : ℂ) (he : ‖e‖=1) :
    ∃u v : ℝ,0≤u ∧ u≤v ∧ v≤c.period ∧
      (2/c.bending t)^2≤(c.endpointHeightDifference (innerSL ℝ e) t u v)^2 := by
  obtain ⟨lo,hi,⟨_,⟨u,hu,eu⟩,⟨v,hv,ev⟩⟩,cost⟩ := c.directional_width_range ht e he
  have ep := c.bending_pos_of_width ht
  have wd : 2/c.bending t ≤ hi-lo := (div_le_iff₀ ep).mpr (by linarith only [cost])
  have sq := pow_le_pow_left₀ (div_nonneg (by norm_num) ep.le) wd 2
  rcases le_total u v with h|h
  · refine ⟨u,v,hu.1,h,hv.2,?_⟩
    simpa only [endpointHeightDifference,eu,ev] using sq
  · refine ⟨v,u,hv.1,h,hu.2,?_⟩
    rw [endpointHeightDifference,eu,ev,show lo-hi= -(hi-lo) by ring,neg_sq]
    exact sq

/-- An unconditional cost for each entire endpoint of a genuine migration,
including zero chosen gaps and zero signed areas. The material curve supplies
its own extremal labels and its own position-defined bending energy. -/
theorem projectedHeight_endpoint_energy_separation (flow : c.IsNormalFEF) (e : ℂ) (he : ‖e‖=1)
    {level g₀ g₁ δ s t : ℝ} (hd : 0<δ) (order : s≤t) (slab : Icc s t⊆I)
    (before : ∀u,inner ℝ e (c.position s u)≤level-g₀)
    (after : ∀u,level+g₁ ≤ inner ℝ e (c.position t u)) :
    g₁*c.regularizedProjectedLength (innerSL ℝ e) δ t+
      g₀*c.regularizedProjectedLength (innerSL ℝ e) δ s+
      max |c.orientedProjectedArea (innerSL ℝ e) t| (δ*(2/c.bending t)^2)+
      max |c.orientedProjectedArea (innerSL ℝ e) s| (δ*(2/c.bending s)^2) ≤
      ∫v in s..t,c.projectedHeightRate (innerSL ℝ e) level δ v := by
  obtain ⟨u,v,hu,huv,hv,hs⟩ := c.pair_from_energy (slab (left_mem_Icc.mpr order)) e he
  obtain ⟨a,b,ha,hab,hb,ht⟩ := c.pair_from_energy (slab (right_mem_Icc.mpr order)) e he
  apply le_trans _ (c.projectedHeight_width_area_separation flow e he hd order slab hu huv hv ha hab hb before after)
  exact add_le_add (add_le_add le_rfl (max_le_max le_rfl (mul_le_mul_of_nonneg_left ht hd.le)))
    (max_le_max le_rfl (mul_le_mul_of_nonneg_left hs hd.le))

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.projectedHeight_endpoint_energy_separation
