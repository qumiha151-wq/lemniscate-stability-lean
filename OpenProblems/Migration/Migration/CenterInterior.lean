import Migration.ExpanderCenterHull
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! The expansion center lies in the ordinary topological interior of
the convex hull of the actual image over one period. -/
noncomputable section
open Set
namespace MigrationGeometry.Adjoint.ClosedExpander
variable {rate L : ℝ} (c : ClosedExpander rate L)

def sliceImage : Set (ℝ × ℝ) := (fun s => (c.x s,c.y s)) '' Icc 0 L

private theorem linear_both_signs {R : ℝ} (hr : 0<rate) (hL : 0<L) (hcap : rate*R^4≤2)
    (hb : ∀ s, (c.x s)^2+(c.y s)^2≤R^2) (F : (ℝ × ℝ) →ₗ[ℝ] ℝ) (hF : F≠0) :
    (∃ z ∈ c.sliceImage, F z<0) ∧ (∃ z ∈ c.sliceImage, 0<F z) := by
  let a := F (1,0)
  let b := F (0,1)
  have rep (z : ℝ × ℝ) : F z=a*z.1+b*z.2 := by
    have hz : z=z.1 • ((1,0) : ℝ × ℝ)+z.2 • ((0,1) : ℝ × ℝ) := by ext <;> simp
    calc
      F z = F (z.1 • ((1,0) : ℝ × ℝ)+z.2 • ((0,1) : ℝ × ℝ)) := congrArg F hz
      _ = _ := by
        rw [map_add,map_smul,map_smul]
        change z.1*a+z.2*b=a*z.1+b*z.2
        ring
  have hne : 0<a^2+b^2 := by
    by_contra! hn
    have ha : a=0 := by nlinarith [sq_nonneg b,sq_nonneg a]
    have hb' : b=0 := by nlinarith [sq_nonneg b,sq_nonneg a]
    apply hF
    apply LinearMap.ext
    intro z
    change F z=0
    rw [rep,ha,hb']
    ring
  obtain ⟨⟨s,hs,hlo⟩,⟨t,ht,hhi⟩⟩ := c.both_sides_of_every_center_line hr hL hcap hb hne
  exact ⟨⟨_,⟨s,hs,rfl⟩,by simpa only [rep] using hlo⟩,
    ⟨_,⟨t,ht,rfl⟩,by simpa only [rep] using hhi⟩⟩

theorem center_mem_interior_convexHull {R : ℝ} (hr : 0<rate) (hL : 0<L) (hcap : rate*R^4≤2)
    (hb : ∀ s, (c.x s)^2+(c.y s)^2≤R^2) :
    (0 : ℝ × ℝ) ∈ interior (convexHull ℝ c.sliceImage) := by
  let A := affineSpan ℝ c.sliceImage
  have hz : (c.x 0,c.y 0) ∈ A := subset_affineSpan ℝ c.sliceImage ⟨0,⟨le_rfl,hL.le⟩,rfl⟩
  have hspan : A=⊤ := by
    by_contra hproper
    have hd : A.direction<⊤ := lt_top_iff_ne_top.mpr (by
      intro hh
      apply hproper
      apply top_unique
      intro z _
      apply (AffineSubspace.vsub_right_mem_direction_iff_mem hz z).mp
      rw [hh]
      trivial)
    obtain ⟨F,hF,hker⟩ := A.direction.exists_le_ker_of_lt_top hd
    obtain ⟨⟨y,hy,hyneg⟩,⟨z,hz',hzpos⟩⟩ := c.linear_both_signs hr hL hcap hb F hF
    have hmem : z -ᵥ y ∈ A.direction := AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ c.sliceImage hz') (subset_affineSpan ℝ c.sliceImage hy)
    have hzero : F (z-y)=0 := hker hmem
    rw [map_sub] at hzero
    linarith
  have hint := interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  by_contra hn
  obtain ⟨F,hF,hbound⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_convexHull ℝ c.sliceImage) hn hint
  have hFl : F.toLinearMap≠0 := by
    intro hz'
    apply hF
    apply ContinuousLinearMap.ext
    intro u
    exact LinearMap.congr_fun hz' u
  obtain ⟨z,hz',hpos⟩ := (c.linear_both_signs hr hL hcap hb F.toLinearMap hFl).2
  have hu := hbound z (subset_convexHull ℝ c.sliceImage hz')
  rw [map_zero] at hu
  exact (not_lt_of_ge hu) hpos

end MigrationGeometry.Adjoint.ClosedExpander
