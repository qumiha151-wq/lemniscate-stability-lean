import SolitonClassification.RamifiedBranchResidual
import SolitonClassification.RamifiedPoleDeck

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature.Ramified

/-- A pole of a branched continuation of ordinary scalar similarity germs has
trivial deck action, for any finite covering degree. No estimate of the
principal Laurent coefficients is part of the hypothesis. -/
theorem finite_pole_deck_of_ordinary_charts {q : ℕ} (hq : 0<q) (a b s₀ : ℂ)
    {f : ℂ→ℂ} {n : ℤ} (mf : MeromorphicAt f 0)
    (order : meromorphicOrderAt f 0=(n:WithTop ℤ)) (pole : n<0)
    (charts : ∀ᶠ w in 𝓝[≠] (0:ℂ), ∃k:ℂ→ℂ, AnalyticAt ℂ k (s₀+w^q) ∧
      (f =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0) :
    ∀r:ℂ,r^q=1 → (fun w=>f (r*w)) =ᶠ[𝓝[≠] (0:ℂ)] f :=
  pole_deck_invariant hq mf order pole (residual_on_puncture hq a b s₀ charts)

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.finite_pole_deck_of_ordinary_charts
