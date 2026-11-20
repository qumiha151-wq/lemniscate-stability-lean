import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped Topology
namespace MigrationGeometry.Flow

/-- Strict directional coverage gives a finite polygon containing the point.
No closedness of the original convex hull is required. -/
theorem mem_convexHull_of_surrounding_directions {A : Set ℂ} {x : ℂ}
    (hs : ∀ e : ℂ, ‖e‖ = 1 → ∃ y ∈ A, inner ℝ e x < inner ℝ e y) :
    x ∈ convexHull ℝ A := by
  classical
  let U : A → Set ℂ := fun z => {e | inner ℝ e x < inner ℝ e (z:ℂ)}
  have hU (z : A) : IsOpen (U z) :=
    isOpen_lt (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  have cov : Metric.sphere (0:ℂ) 1 ⊆ ⋃ z, U z := by
    intro e he
    obtain ⟨y,hy,h⟩ := hs e (by simpa [Metric.mem_sphere] using he)
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,h⟩
  obtain ⟨t,ht⟩ := (isCompact_sphere (0:ℂ) 1).elim_finite_subcover U hU cov
  let B := (Subtype.val : A → ℂ) '' (t : Set A)
  have hfinite : B.Finite := t.finite_toSet.image _
  have hsub : B ⊆ A := fun _ ⟨z,_,he⟩ => he ▸ z.property
  have hit (e : ℂ) (he : ‖e‖=1) : ∃ y ∈ B, inner ℝ e x < inner ℝ e y := by
    have hv := ht (show e ∈ Metric.sphere (0:ℂ) 1 by simpa [Metric.mem_sphere])
    obtain ⟨z,hz⟩ := mem_iUnion.mp hv
    obtain ⟨htz,hu⟩ := mem_iUnion.mp hz
    exact ⟨z,⟨z,htz,rfl⟩,hu⟩
  apply convexHull_mono hsub
  by_contra hx
  obtain ⟨f,r,hr,hrx⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ B)
    (hfinite.isClosed_convexHull ℝ) hx
  let w := (InnerProductSpace.toDual ℝ ℂ).symm f
  have hwi (y : ℂ) : inner ℝ w y = f y := InnerProductSpace.toDual_symm_apply
  have hw : w ≠ 0 := by
    intro h
    obtain ⟨z,hz,_⟩ := hit 1 (by simp)
    have hz' := hr z (subset_convexHull ℝ B hz)
    rw [← hwi z,h] at hz'
    rw [← hwi x,h] at hrx
    simp only [inner_zero_left] at hz' hrx
    linarith
  have hw0 := norm_pos_iff.mpr hw
  obtain ⟨y,hy,hsep⟩ := hit (‖w‖⁻¹ • w) (by simp [hw0.ne'])
  rw [real_inner_smul_left,real_inner_smul_left,hwi x,hwi y] at hsep
  have h := (mul_lt_mul_iff_right₀ (inv_pos.mpr hw0)).mp hsep
  exact (not_lt_of_ge (le_of_lt ((hr y (subset_convexHull ℝ B hy)).trans hrx))) h

/-- A strict margin between the inner and outer support radii gives
inclusion of the entire physical closed ball in the actual convex hull. -/
theorem closedBall_subset_convexHull_of_directional_margin {A : Set ℂ} {p : ℂ}
    {r R : ℝ} (hgap : r < R)
    (hs : ∀ e : ℂ, ‖e‖=1 → ∃ y ∈ A, inner ℝ e p + R ≤ inner ℝ e y) :
    Metric.closedBall p r ⊆ convexHull ℝ A := by
  intro x hx
  apply mem_convexHull_of_surrounding_directions
  intro e he
  obtain ⟨y,hy,hs'⟩ := hs e he
  refine ⟨y,hy,?_⟩
  have hnorm : ‖x-p‖ ≤ r := by simpa [Metric.mem_closedBall,dist_eq_norm] using hx
  have h := real_inner_le_norm e (x-p)
  rw [inner_sub_right,he,one_mul] at h
  linarith

#print axioms closedBall_subset_convexHull_of_directional_margin
end MigrationGeometry.Flow
