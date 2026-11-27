import SolitonClassification.Rotating.IntegerPhysicalHull
import SolitonClassification.Rotating.IntegerHullIndexed

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Set NormalEvolution DyadicReset

/-- A primitive rotating self-similar solution in physical time.
The curvature, the force and the unit normal in the evolution are computed
from the time-slice coordinate derivatives. -/
structure PrimitiveEvolution (P : Seed) : Prop where
  length_range : 60 < P.L ∧ P.L < 62
  rotation_range : 1/10 < P.b ∧ P.b < 11/100
  positive_curvature : 7 < P.I.k 0
  negative_curvature : ∃s, P.I.k s < 0
  rotation_contribution : P.b*(P.I.x 0*deriv P.I.x 0+P.I.y 0*deriv P.I.y 0)≠0
  shortest_period : IsLeast {h : ℝ | 0<h ∧ Function.Periodic P.I.x h ∧ Function.Periodic P.I.y h} P.L
  initial : ∀s, normalX P 0 s=P.I.x s ∧ normalY P 0 s=P.I.y s
  physical_flow : IsPureNormalElasticEvolution P.L (normalX P) (normalY P)
  actual_length : ∀t, 0≤t → (∫s in 0..P.L,curveSpeed (normalX P t) (normalY P t) s)=dilationScale t*P.L
  similarity_image : ∀t, 0≤t → sliceImage P t=
    planarSimilarity (dilationScale t) (P.b*logClock t) '' initialImage P
  expanding_disk : ∀t, 0≤t → ∀z : ℝ×ℝ, z.1^2+z.2^2≤(dilationScale t/20)^2 →
    z∈convexHull ℝ (sliceImage P t)

theorem physical_evolution_of_indexed_rows
    (p : ℕ → TapeRow Middle.hn) (m : ℕ → TapeRow (-Middle.hn))
    (hp : ∀i : ℕ, i<4000 → (p i).left=GridPlus.atNode i ∧ (p i).right=GridPlus.atNode (i+1))
    (hm : ∀i : ℕ, i<4000 → (m i).left=GridMinus.atNode i ∧ (m i).right=GridMinus.atNode (i+1)) :
    ∃P : Seed, PrimitiveEvolution P := by
  obtain ⟨c,hc,I,lo,hi,bl,bh,kp,kn,rotation,least,disk⟩ := square_immersion_from_indexed_rows p m hp hm
  let P : Seed := ⟨c 4,2*c 2,I,by linarith⟩
  refine ⟨P,⟨⟨lo,hi⟩,⟨bl,bh⟩,kp,kn,rotation,least,?_,normalEvolution_is_pure_normal P,
    fun t _ => normal_length P t,fun t _ => physical_image_eq P t,?_⟩⟩
  · exact fun s => ⟨normalX_initial P s,normalY_initial P s⟩
  · exact fun t _ => physical_disk_of_square P disk t

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.physical_evolution_of_indexed_rows
