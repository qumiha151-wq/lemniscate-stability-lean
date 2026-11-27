import SolitonClassification.Rotating.IntegerPhysicalFromRows
import SolitonClassification.Rotating.PeriodicSimilarityGenerator

namespace SolitonClassification.Rotating.IntegerTarget.Physical
noncomputable section
open Real
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A planar infinitesimal similarity tangent to a nonconstant-curvature
closed immersion vanishes, including its translation coefficients. -/
theorem tangent_generator_vanishes (P : Seed) {a b u v : ℝ}
    (different : ∃s t, P.I.k s≠P.I.k t)
    (tangent : ∀s, -(a*P.I.x s-b*P.I.y s+u)*sin (P.I.theta s)+
      (b*P.I.x s+a*P.I.y s+v)*cos (P.I.theta s)=0) :
    a=0 ∧ b=0 ∧ u=0 ∧ v=0 := by
  apply ClosedSimilarity.tangent_similarity_zero P.positive P.I.smoothX P.I.smoothY
    P.I.periodX P.I.periodY P.I.speed
  · obtain ⟨s,t,ne⟩ := different
    exact ⟨s,t,by simpa only [P.I.curvature] using ne⟩
  · intro s
    rw [(P.I.tangentX s).deriv,(P.I.tangentY s).deriv]
    exact tangent s

def generatorNormal (P : Seed) (a b u v s : ℝ) :=
  -(a*P.I.x s-b*P.I.y s+u)*sin (P.I.theta s)+
    (b*P.I.x s+a*P.I.y s+v)*cos (P.I.theta s)

/-- All four similarity coefficients are identified by the physical force on
this primitive profile. In particular a different center cannot erase rotation. -/
theorem PrimitiveEvolution.unique_generator {P : Seed} (G : PrimitiveEvolution P)
    {a b u v : ℝ} (generator : ∀s, deriv (deriv P.I.k) s+(P.I.k s)^3/2 =
      -generatorNormal P a b u v s) : a=1 ∧ b=P.b ∧ u=0 ∧ v=0 := by
  obtain ⟨t,ht⟩ := G.negative_curvature
  have different : P.I.k 0≠P.I.k t := by linarith [G.positive_curvature]
  have h := tangent_generator_vanishes (a:=a-1) (b:=b-P.b) (u:=u) (v:=v) P ⟨0,t,different⟩ (by
    intro s
    have given := generator s
    have actual := P.I.soliton s
    rw [(P.I.tangentX s).deriv,(P.I.tangentY s).deriv] at actual
    dsimp only [generatorNormal] at given
    linear_combination given-actual)
  exact ⟨sub_eq_zero.mp h.1,sub_eq_zero.mp h.2.1,h.2.2⟩

end
end SolitonClassification.Rotating.IntegerTarget.Physical
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.tangent_generator_vanishes
#print axioms SolitonClassification.Rotating.IntegerTarget.Physical.PrimitiveEvolution.unique_generator
