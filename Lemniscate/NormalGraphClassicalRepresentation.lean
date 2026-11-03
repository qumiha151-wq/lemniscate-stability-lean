import Lemniscate.NormalGraphSobolevFlow
import Lemniscate.NormalGraphRationalIdentities

/-! Classical representation of the Sobolev normal-graph equation.

The fourth weak derivative is required to have an explicitly supplied
continuous representative in this theorem. General H4 data do not have this
additional continuity. The continuous right-hand side is the same generic
rational flow already used for the lower-order coefficient.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 800000 in
theorem circle_normal_graph_flow_classical_representation
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (f : CircleSobolevSpace T 4) (f₄ : C(AddCircle T, ℂ))
    (hf₄ : circleSobolevCoordinate T 4 4 f = circleContinuousL2 T f₄)
    (hf : f ∈ circleNormalGraphDomain T K) :
    let Z := circleNormalGraphCoordinates T f
    circleNormalGraphFlow T K c f = circleContinuousL2 T
        (normalGraphRationalFlow K c ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • f₄⟩) ∧
      ∀ x : AddCircle T,
        normalGraphRationalFlow K c ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • f₄⟩ x =
          normalGraphRationalFlow (R := ℂ)
            ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩ c
            ⟨Z 0 x,Z 1 x,Z 2 x,Z 3 x,4*f₄ x⟩ := by
  let Z := circleNormalGraphCoordinates T f
  let J : HeightJetOver C(AddCircle T, ℂ) := ⟨Z 0,Z 1,Z 2,Z 3,(4:ℂ) • f₄⟩
  have hz : Z ∈ normalGraphCoefficientDomain T K := hf
  have hA : IsUnit (graphA K J) := hz.1
  have hH : IsUnit (graphMetricSquared K J) := hz.2
  have hsplit : normalGraphRationalFlow K c J =
      normalGraphPrincipalCoefficient T K Z*((4:ℂ) • f₄)+
        normalGraphLowerOrderCoefficient T K c Z :=
    normal_graph_rational_flow_quasilinear K c J hA
  have hfourth : (4:ℂ) • circleSobolevCoordinate T 4 4 f =
      circleContinuousL2 T ((4:ℂ) • f₄) := by
    rw [hf₄]
    simp only [circleContinuousL2,map_smul]
  refine ⟨?_,?_⟩
  · change circleMultiplyL2 T (normalGraphPrincipalCoefficient T K Z)
        ((4:ℂ) • circleSobolevCoordinate T 4 4 f)+
          circleContinuousL2 T (normalGraphLowerOrderCoefficient T K c Z) =
        circleContinuousL2 T (normalGraphRationalFlow K c J)
    rw [hfourth,circle_multiply_l2_continuous,hsplit]
    simp only [circleContinuousL2,map_add]
  · intro x
    have hx := normal_graph_rational_flow_apply T K c J hA hH x
    simpa only [J,ContinuousMap.smul_apply,smul_eq_mul] using hx

end Lemniscate
