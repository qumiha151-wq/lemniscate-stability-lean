import Lemniscate.NormalGraphSobolevFlow
import Lemniscate.NormalGraphRationalStar
import Lemniscate.PeriodicSobolevConjugation

/-! Conjugation equivariance of the rational complexified H4 normal-graph flow.
The background is conjugated field by field. This is an identity of the
function and its domain; preservation of real PDE solutions additionally
requires uniqueness of those solutions.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

private theorem circle_sobolev_continuous_jet_star
    (f : CircleSobolevSpace T 4) (j : Fin 4) :
    circleSobolevContinuousJet T (circleSobolevConjugation T 4 f) j =
      star (circleSobolevContinuousJet T f j) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle
  change circleContinuousL2 T (circleSobolevContinuousJet T (circleSobolevConjugation T 4 f) j) =
    circleContinuousL2 T (star (circleSobolevContinuousJet T f j))
  rw [circle_sobolev_continuous_jet_l2,circle_continuous_l2_star,
    circle_sobolev_conjugation_coordinate,circle_sobolev_continuous_jet_l2]

private theorem circle_normal_graph_coordinates_star (f : CircleSobolevSpace T 4) :
    circleNormalGraphCoordinates T (circleSobolevConjugation T 4 f) =
      fun j => star (circleNormalGraphCoordinates T f j) := by
  funext j
  rw [circle_normal_graph_coordinates,circle_normal_graph_coordinates]
  fin_cases j <;> simp [circle_sobolev_continuous_jet_star,star_smul,
    Complex.star_def,Complex.conj_ofReal]

private theorem circle_conjugate_multiply_general
    (a : C(AddCircle T, ℂ)) (f : CircleL2 T) :
    circleConjugate T (circleMultiplyL2 T a f) =
      circleMultiplyL2 T (star a) (circleConjugate T f) := by
  apply Lp.ext
  filter_upwards [circle_conjugate_ae T (circleMultiplyL2 T a f),
    circle_multiply_l2_ae T a f,circle_conjugate_ae T f,
    circle_multiply_l2_ae T (star a) (circleConjugate T f)] with x hc hm hf hstar
  rw [hc,hm,hstar,hf,map_mul]
  rfl

theorem circle_normal_graph_flow_conjugation
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ) (f : CircleSobolevSpace T 4) :
    let Kstar : BackgroundJetOver C(AddCircle T, ℂ) :=
      ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩
    circleConjugate T (circleNormalGraphFlow T K c f) =
        circleNormalGraphFlow T Kstar c (circleSobolevConjugation T 4 f) ∧
      (f ∈ circleNormalGraphDomain T K ↔
        circleSobolevConjugation T 4 f ∈ circleNormalGraphDomain T Kstar) := by
  let Kstar : BackgroundJetOver C(AddCircle T, ℂ) :=
    ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩
  let fstar := circleSobolevConjugation T 4 f
  let Z := circleNormalGraphCoordinates T f
  let Zstar : Fin 4 → C(AddCircle T, ℂ) := fun j => star (Z j)
  have hZ : circleNormalGraphCoordinates T fstar = Zstar :=
    circle_normal_graph_coordinates_star T f
  have hmul (a b : C(AddCircle T, ℂ)) : star (a*b) = star a*star b :=
    (starRingEnd C(AddCircle T, ℂ)).map_mul a b
  have hA : graphA Kstar ⟨Zstar 0,Zstar 1,Zstar 2,Zstar 3,0⟩ =
      star (graphA K ⟨Z 0,Z 1,Z 2,Z 3,0⟩) := by
    simp only [graphA,Kstar,Zstar,star_sub,star_one,hmul]
  have hH : graphMetricSquared Kstar ⟨Zstar 0,Zstar 1,Zstar 2,Zstar 3,0⟩ =
      star (graphMetricSquared K ⟨Z 0,Z 1,Z 2,Z 3,0⟩) := by
    simp only [graphMetricSquared,graphA,Kstar,Zstar,star_add,star_pow,
      star_sub,star_one,hmul]
  have hprincipal : star (normalGraphPrincipalCoefficient T K Z) =
      normalGraphPrincipalCoefficient T Kstar Zstar := by
    change star (-((Ring.inverse (graphMetricSquared K ⟨Z 0,Z 1,Z 2,Z 3,0⟩))^2)) =
      -((Ring.inverse (graphMetricSquared Kstar ⟨Zstar 0,Zstar 1,Zstar 2,Zstar 3,0⟩))^2)
    rw [hH]
    simp only [star_neg,star_pow,← Ring.inverse_star]
  have hlower : star (normalGraphLowerOrderCoefficient T K c Z) =
      normalGraphLowerOrderCoefficient T Kstar c Zstar := by
    simpa only [normalGraphLowerOrderCoefficient,normalGraphLowerOrderCoefficientOver,Kstar,Zstar,star_zero] using
      normal_graph_rational_flow_star K c ⟨Z 0,Z 1,Z 2,Z 3,0⟩
  have hfourth : circleConjugate T ((4:ℂ) • circleSobolevCoordinate T 4 4 f) =
      (4:ℂ) • circleSobolevCoordinate T 4 4 fstar := by
    simp only [fstar,circle_conjugate_smul,circle_sobolev_conjugation_coordinate,
      map_ofNat]
  refine ⟨?_,?_⟩
  · change circleConjugate T (circleNormalGraphFlow T K c f) =
      circleNormalGraphFlow T Kstar c fstar
    simp only [circleNormalGraphFlow,circle_coefficient_multiply_l2_apply,
      circle_conjugate_add,circle_conjugate_multiply_general,
      ← circle_continuous_l2_star,hZ,hfourth]
    change circleMultiplyL2 T (star (normalGraphPrincipalCoefficient T K Z))
        ((4:ℂ) • circleSobolevCoordinate T 4 4 fstar) +
        circleContinuousL2 T (star (normalGraphLowerOrderCoefficient T K c Z)) =
      circleMultiplyL2 T (normalGraphPrincipalCoefficient T Kstar Zstar)
        ((4:ℂ) • circleSobolevCoordinate T 4 4 fstar) +
        circleContinuousL2 T (normalGraphLowerOrderCoefficient T Kstar c Zstar)
    rw [hprincipal,hlower]
  · change Z ∈ normalGraphCoefficientDomain T K ↔
      circleNormalGraphCoordinates T fstar ∈ normalGraphCoefficientDomain T Kstar
    rw [hZ]
    change (IsUnit (graphA K ⟨Z 0,Z 1,Z 2,Z 3,0⟩) ∧
        IsUnit (graphMetricSquared K ⟨Z 0,Z 1,Z 2,Z 3,0⟩)) ↔
      (IsUnit (graphA Kstar ⟨Zstar 0,Zstar 1,Zstar 2,Zstar 3,0⟩) ∧
        IsUnit (graphMetricSquared Kstar ⟨Zstar 0,Zstar 1,Zstar 2,Zstar 3,0⟩))
    simp only [hA,hH,isUnit_star]

end Lemniscate
