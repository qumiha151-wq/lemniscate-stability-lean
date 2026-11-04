import Lemniscate.NormalGraphSobolevFlow
import Lemniscate.NormalGraphLowerCoefficients

/-! The value and first physical derivative of an H2 normal graph.
The regularity conditions A and H involve only these two continuous
coordinates. Consequently an H2 neighborhood controls regularity for H4
graphs, independently of the sizes of their higher derivatives.
-/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

/-- The actual continuous representatives [h,sqrt(2)*h_x] of H2 data. -/
def circleNormalGraphLowCoordinates :
    CircleSobolevSpace T 2 →L[ℂ] (Fin 2 → C(AddCircle T, ℂ)) :=
  ContinuousLinearMap.pi fun j =>
    (![1,((Real.sqrt 2:ℝ):ℂ)] j) •
      ((circleSobolevH1Embedding T).comp
        (![circleSobolevInclusion T 1,circleSobolevDerivative T 1] j))

theorem circle_normal_graph_low_coordinates (f : CircleSobolevSpace T 2) :
    circleNormalGraphLowCoordinates T f =
      ![circleSobolevH1Embedding T (circleSobolevInclusion T 1 f),
        ((Real.sqrt 2:ℝ):ℂ) •
          circleSobolevH1Embedding T (circleSobolevDerivative T 1 f)] := by
  funext j
  fin_cases j <;> simp [circleNormalGraphLowCoordinates]

/-- The first two H4 coordinates depend only on the H2 inclusion. -/
theorem circle_normal_graph_coordinates_low (f : CircleSobolevSpace T 4) (j : Fin 2) :
    circleNormalGraphCoordinates T f j.castSucc.castSucc =
      circleNormalGraphLowCoordinates T
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) j := by
  fin_cases j <;> rfl

theorem circle_normal_graph_domain_iff_low
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (f : CircleSobolevSpace T 4) :
    f ∈ circleNormalGraphDomain T K ↔
      circleNormalGraphLowCoordinates T
          (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) ∈
        normalGraphLowerCoefficientDomain T K := by
  have h₀ : circleNormalGraphCoordinates T f 0 =
      circleNormalGraphLowCoordinates T
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) 0 :=
    circle_normal_graph_coordinates_low T f 0
  have h₁ : circleNormalGraphCoordinates T f 1 =
      circleNormalGraphLowCoordinates T
        (circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)) 1 :=
    circle_normal_graph_coordinates_low T f 1
  change
    (IsUnit (1-K.k*(circleNormalGraphCoordinates T f 0)) ∧
      IsUnit ((1-K.k*(circleNormalGraphCoordinates T f 0))^2+
        (circleNormalGraphCoordinates T f 1)^2)) ↔ _
  rw [h₀,h₁]
  rfl

/-- Smallness in the H2 norm alone ensures that the H4 graph is in the
open domain of the rational normal-graph equation. -/
theorem circle_normal_graph_h2_small_domain
    (K : BackgroundJetOver C(AddCircle T, ℂ)) :
    ∃ δ > 0, ∀ f : CircleSobolevSpace T 4,
      ‖circleSobolevInclusion T 2 (circleSobolevInclusion T 3 f)‖ < δ →
        f ∈ circleNormalGraphDomain T K := by
  obtain ⟨hopen,hzero,_⟩ := normal_graph_lower_coefficients_smooth_over C(AddCircle T, ℂ) K 0
  have hnhds : normalGraphLowerCoefficientDomain T K ∈
      𝓝 (0 : Fin 2 → C(AddCircle T, ℂ)) := hopen.mem_nhds hzero
  have hpre : (circleNormalGraphLowCoordinates T) ⁻¹'
      normalGraphLowerCoefficientDomain T K ∈ 𝓝 (0 : CircleSobolevSpace T 2) := by
    apply (circleNormalGraphLowCoordinates T).continuous.continuousAt.preimage_mem_nhds
    simpa only [map_zero] using hnhds
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨δ,hδ,?_⟩
  intro f hf
  apply (circle_normal_graph_domain_iff_low T K f).mpr
  apply hball
  simpa only [Metric.mem_ball,dist_eq_norm,sub_zero] using hf

end Lemniscate
