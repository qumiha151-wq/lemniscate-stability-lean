import Lemniscate.NormalGraphLowSobolevCoordinates

/-! The complete H4 normal-graph equation as L2 products.

All six lower-order coefficients depend only on the actual H2 inclusion.
The physical second and third derivatives carry the factors 2 and 2*sqrt(2).
The fourth derivative is kept in L2 throughout; no continuous fourth
derivative is introduced.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

set_option maxHeartbeats 800000 in
theorem circle_normal_graph_flow_polynomial
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (f : CircleSobolevSpace T 4) (hf : f ∈ circleNormalGraphDomain T K) :
    let low := circleNormalGraphLowCoordinates T
      (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))
    let B := normalGraphLowerCoefficientMap T K c low
    let v := (2:ℂ) • circleSobolevContinuousJet T f 2
    let V := (2:ℂ) • circleSobolevCoordinate T 4 2 f
    let W := ((2*Real.sqrt 2:ℝ):ℂ) • circleSobolevCoordinate T 4 3 f
    circleNormalGraphFlow T K c f =
      circleCoefficientMultiplyL2 T
          (normalGraphPrincipalCoefficient T K (circleNormalGraphCoordinates T f))
          ((4:ℂ) • circleSobolevCoordinate T 4 4 f)+
        circleContinuousL2 T (B 0)+
        circleMultiplyL2 T (B 1) V+
        circleMultiplyL2 T (B 2*v) V+
        circleMultiplyL2 T (B 3*v^2) V+
        circleMultiplyL2 T (B 4) W+
        circleMultiplyL2 T (B 5*v) W := by
  let Z := circleNormalGraphCoordinates T f
  let low := circleNormalGraphLowCoordinates T
    (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f))
  let B := normalGraphLowerCoefficientMap T K c low
  let v := (2:ℂ) • circleSobolevContinuousJet T f 2
  let w := ((2*Real.sqrt 2:ℝ):ℂ) • circleSobolevContinuousJet T f 3
  let V := (2:ℂ) • circleSobolevCoordinate T 4 2 f
  let W := ((2*Real.sqrt 2:ℝ):ℂ) • circleSobolevCoordinate T 4 3 f
  have hz : Z ∈ normalGraphCoefficientDomain T K := hf
  have h₀ : Z 0 = low 0 := circle_normal_graph_coordinates_low T f 0
  have h₁ : Z 1 = low 1 := circle_normal_graph_coordinates_low T f 1
  have hlow : ![Z 0,Z 1] = low := by
    funext j
    fin_cases j
    · exact h₀
    · exact h₁
  have hZ₂ : Z 2 = v := by
    change circleNormalGraphCoordinates T f 2 = v
    rw [circle_normal_graph_coordinates]
    rfl
  have hZ₃ : Z 3 = w := by
    change circleNormalGraphCoordinates T f 3 = w
    rw [circle_normal_graph_coordinates]
    rfl
  have hpoly : normalGraphLowerOrderCoefficient T K c Z =
      B 0+B 1*v+B 2*v^2+B 3*v^3+B 4*w+B 5*v*w := by
    simpa only [hlow,hZ₂,hZ₃] using
      normal_graph_lower_order_coefficient_polynomial T K c Z hz
  have hv : circleContinuousL2 T v = V := by
    simpa only [v,V,circleContinuousL2,map_smul] using!
      congrArg (fun u : CircleL2 T => (2:ℂ) • u)
        (circle_sobolev_continuous_jet_l2 T f 2)
  have hw : circleContinuousL2 T w = W := by
    simpa only [w,W,circleContinuousL2,map_smul] using!
      congrArg (fun u : CircleL2 T => ((2*Real.sqrt 2:ℝ):ℂ) • u)
        (circle_sobolev_continuous_jet_l2 T f 3)
  have hquadratic : B 2*v^2 = (B 2*v)*v := by ring
  have hcubic : B 3*v^3 = (B 3*v^2)*v := by ring
  have hterms : circleContinuousL2 T (normalGraphLowerOrderCoefficient T K c Z) =
      circleContinuousL2 T (B 0)+
        circleMultiplyL2 T (B 1) V+
        circleMultiplyL2 T (B 2*v) V+
        circleMultiplyL2 T (B 3*v^2) V+
        circleMultiplyL2 T (B 4) W+
        circleMultiplyL2 T (B 5*v) W := by
    rw [hpoly,hquadratic,hcubic,← hv,← hw]
    simp only [circle_multiply_l2_continuous]
    simp only [circleContinuousL2,map_add]
  simpa only [circleNormalGraphFlow,Z,low,B,v,V,W,add_assoc] using
    congrArg (fun u : CircleL2 T =>
      circleCoefficientMultiplyL2 T (normalGraphPrincipalCoefficient T K Z)
        ((4:ℂ) • circleSobolevCoordinate T 4 4 f)+u) hterms

end Lemniscate
