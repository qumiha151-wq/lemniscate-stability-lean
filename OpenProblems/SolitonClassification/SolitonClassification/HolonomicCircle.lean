import SolitonClassification.HolonomicExpansion
import SolitonClassification.HolonomicRegularity
import SolitonClassification.TrigCurvatureCircle

noncomputable section
namespace ClosedSimilarity.ClosedUnitFrenetCurve

/-- A polynomial-coefficient linear differential equation for the actual arclength
curvature forces the entire smooth closed similarity profile to be a covered circle. -/
theorem dfinite_curvature_circle (c : ClosedUnitFrenetCurve) (a b vx vy : ℝ)
    (law : ∀ s, c.positionForce s = -a*c.normalSupport s-b*c.tangentSupport s+vx*c.ty s-vy*c.tx s)
    (J : Finset ℕ) (p : ℕ → Polynomial ℂ) (nonzero : ∃ j ∈ J, p j ≠ 0)
    (ode : ∀ s : ℝ, ∑ j ∈ J, (p j).eval (s : ℂ)*((iteratedDeriv j c.k s : ℝ) : ℂ) = 0) :
    ∃ (K : ℝ) (O A : ℂ), K ≠ 0 ∧ A ≠ 0 ∧ (∀ s, c.k s=K) ∧
      ∀ s : ℝ, (c.x s:ℂ)+(c.y s:ℂ)*Complex.I = O+A*Complex.exp (((K*s:ℝ):ℂ)*Complex.I) := by
  have regular := c.similarity_curvature_smooth a b vx vy law
  obtain ⟨S,coeff,fourier⟩ := Holonomic.periodic_dfinite_expansion c.period_pos regular c.periodic_k J p nonzero ode
  exact c.finite_fourier_circle a b vx vy law c.period c.period_pos S coeff fourier

end ClosedSimilarity.ClosedUnitFrenetCurve
#print axioms ClosedSimilarity.ClosedUnitFrenetCurve.dfinite_curvature_circle

