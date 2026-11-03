import Lemniscate.NormalGraphPolynomial
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Real.Star

/-! Conjugation of the rational normal-graph expression.
The total ring inverse commutes with star, without a unit hypothesis.
This algebraic identity does not assert uniqueness of a flow solution. -/
noncomputable section
namespace Lemniscate

private def backgroundJetStar {R : Type*} [Star R]
    (K : BackgroundJetOver R) : BackgroundJetOver R :=
  ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩

private def heightJetStar {R : Type*} [Star R]
    (h : HeightJetOver R) : HeightJetOver R :=
  ⟨star h.h,star h.hs,star h.hss,star h.hsss,star h.hssss⟩

/-- For a real background the starred background fields reduce to the original
ones, so conjugating the output agrees with conjugating every height field. -/
theorem normal_graph_rational_flow_star
    {R : Type*} [CommRing R] [StarRing R] [Algebra ℝ R] [StarModule ℝ R]
    (K : BackgroundJetOver R) (c : ℝ) (h : HeightJetOver R) :
    star (normalGraphRationalFlow K c h) = normalGraphRationalFlow
      ⟨star K.k,star K.ks,star K.kss,star K.ksss,star K.eta,star K.b⟩ c
      ⟨star h.h,star h.hs,star h.hss,star h.hsss,star h.hssss⟩ := by
  change star (normalGraphRationalFlow K c h) =
    normalGraphRationalFlow (backgroundJetStar K) c (heightJetStar h)
  have hmul (a b : R) : star (a*b) = star a*star b :=
    (starRingEnd R).map_mul a b
  dsimp only [normalGraphRationalFlow,backgroundJetStar,heightJetStar,
    graphCurvatureNumeratorSS,graphCurvatureNumeratorS,graphCurvatureNumerator,
    graphMetricSquaredSS,graphMetricSquaredS,graphMetricSquared,
    graphSupportNumerator,graphAss,graphAs,graphA]
  simp only [hmul,star_neg,star_add,star_sub,star_pow,star_smul,
    star_trivial,star_one,star_ofNat,← Ring.inverse_star] <;> ring

end Lemniscate
