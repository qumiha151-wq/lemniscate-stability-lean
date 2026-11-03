import Lemniscate.NormalGraphPolynomial
import Lemniscate.PeriodicCoefficientAlgebra

/-! The principal fourth derivative and pointwise meaning of the rational
normal-graph flow. Evaluation of inverse coefficient functions requires units. -/
noncomputable section
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

private def backgroundJetAt (K : BackgroundJetOver C(AddCircle T, ℂ))
    (x : AddCircle T) : BackgroundJetOver ℂ :=
  ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩

private def heightJetAt (h : HeightJetOver C(AddCircle T, ℂ))
    (x : AddCircle T) : HeightJetOver ℂ :=
  ⟨h.h x,h.hs x,h.hss x,h.hsss x,h.hssss x⟩

/-- A unit coefficient function has the expected pointwise scalar inverse;
both A and H must be units for evaluation of the full rational flow. -/
theorem normal_graph_rational_flow_apply
    (K : BackgroundJetOver C(AddCircle T, ℂ)) (c : ℝ)
    (h : HeightJetOver C(AddCircle T, ℂ))
    (hA : IsUnit (graphA K h)) (hH : IsUnit (graphMetricSquared K h))
    (x : AddCircle T) :
    normalGraphRationalFlow K c h x = normalGraphRationalFlow (R := ℂ)
      ⟨K.k x,K.ks x,K.kss x,K.ksss x,K.eta x,K.b x⟩ c
      ⟨h.h x,h.hs x,h.hss x,h.hsss x,h.hssss x⟩ := by
  change normalGraphRationalFlow K c h x =
    normalGraphRationalFlow (backgroundJetAt T K x) c (heightJetAt T h x)
  have hAi := continuous_map_ring_inverse_apply (graphA K h) hA x
  have hHi := continuous_map_ring_inverse_apply (graphMetricSquared K h) hH x
  simp only [normalGraphRationalFlow,ContinuousMap.neg_apply,ContinuousMap.mul_apply,
    ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.pow_apply,
    ContinuousMap.smul_apply,hAi,hHi,Ring.inverse_eq_inv]
  simp only [backgroundJetAt,heightJetAt,graphCurvatureNumeratorSS,
    graphCurvatureNumeratorS,graphCurvatureNumerator,graphMetricSquaredSS,
    graphMetricSquaredS,graphMetricSquared,graphSupportNumerator,
    graphAss,graphAs,graphA,ContinuousMap.neg_apply,ContinuousMap.mul_apply,
    ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.pow_apply,
    ContinuousMap.one_apply,ContinuousMap.smul_apply] <;> rfl

end Lemniscate
