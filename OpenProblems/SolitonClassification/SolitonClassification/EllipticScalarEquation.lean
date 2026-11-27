import SolitonClassification.MeromorphicScalarEquation

noncomputable section
open Filter
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- Elliptic continuations satisfy the physical fourth-order equation as
a special case of the meromorphic continuation theorem. -/
theorem residual_germ_of_extension {a b L : ℝ} (p : PeriodicSupportProfile a b L)
    (e : EllipticExtension p.k) (z : ℂ) :
    ordinaryResidual a b e.extension =ᶠ[𝓝[≠] z] fun _=>0 :=
  residual_germ_of_meromorphic_trace p (fun x=>(e.normal x).meromorphicAt)
    e.analytic_real e.restrict_real z

end ClosedSimilarity.MeromorphicCurvature
