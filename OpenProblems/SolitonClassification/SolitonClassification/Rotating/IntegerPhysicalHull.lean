import SolitonClassification.Rotating.IntegerPhysicalEvolution
import Mathlib.Analysis.Convex.Hull

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Real Set NormalEvolution
set_option backward.isDefEq.respectTransparency false

def planarSimilarity (r θ : ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun z := (r*(cos θ*z.1-sin θ*z.2),r*(sin θ*z.1+cos θ*z.2))
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' c x := by ext <;> dsimp <;> ring

def initialImage (P : Seed) := range (fun s => (P.I.x s,P.I.y s))
def sliceImage (P : Seed) (t : ℝ) := range (fun s => (normalX P t s,normalY P t s))

/-- Exact equality of images, since the smooth reparametrization is onto. -/
theorem physical_image_eq (P : Seed) (t : ℝ) :
    sliceImage P t=planarSimilarity (dilationScale t) (P.b*logClock t) '' initialImage P := by
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨_,⟨normalParameter P (logClock t) s,rfl⟩,rfl⟩
  · rintro ⟨_,⟨s,rfl⟩,rfl⟩
    obtain ⟨v,hv⟩ := (scalarFlow_bijective (physicalField P) (logClock t)).surjective s
    change normalParameter P (logClock t) v=s at hv
    refine ⟨v,?_⟩
    change (_,_)=(dilationScale t*(cos (P.b*logClock t)*P.I.x s-sin (P.b*logClock t)*P.I.y s),
      dilationScale t*(sin (P.b*logClock t)*P.I.x s+cos (P.b*logClock t)*P.I.y s))
    dsimp only [normalX,normalY,normalLogX,normalLogY,dilationScale]
    rw [hv]

theorem physical_disk_of_square (P : Seed)
    (inside : ∀w : ℝ×ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (initialImage P))
    (t : ℝ) (z : ℝ×ℝ) (hz : z.1^2+z.2^2≤(dilationScale t/20)^2) :
    z∈convexHull ℝ (sliceImage P t) := by
  let r := dilationScale t
  let c := cos (P.b*logClock t)
  let s := sin (P.b*logClock t)
  let w : ℝ×ℝ := ((c*z.1+s*z.2)/r,(-s*z.1+c*z.2)/r)
  have hcs : s^2+c^2=1 := sin_sq_add_cos_sq _
  have hr : 0<r := dilationScale_pos _
  have hw : w.1^2+w.2^2≤(1/20:ℝ)^2 := by
    have he : (c*z.1+s*z.2)^2+(-s*z.1+c*z.2)^2=z.1^2+z.2^2 := by
      linear_combination (z.1^2+z.2^2)*hcs
    change ((c*z.1+s*z.2)/r)^2+((-s*z.1+c*z.2)/r)^2≤_
    rw [div_pow,div_pow,←add_div,he,div_le_iff₀ (sq_pos_of_pos hr)]
    change z.1^2+z.2^2≤(r/20)^2 at hz
    linarith
  have wx : |w.1|≤1/20 := le_of_sq_le_sq (by rw [sq_abs]; linarith [sq_nonneg w.2]) (by norm_num)
  have wy : |w.2|≤1/20 := le_of_sq_le_sq (by rw [sq_abs]; linarith [sq_nonneg w.1]) (by norm_num)
  rw [physical_image_eq,← LinearMap.image_convexHull]
  refine ⟨w,inside w wx wy,?_⟩
  change (r*(c*w.1-s*w.2),r*(s*w.1+c*w.2))=z
  ext <;> dsimp only [w] <;> field_simp [hr.ne'] <;> first
    | linear_combination z.1*hcs
    | linear_combination z.2*hcs

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.physical_disk_of_square
