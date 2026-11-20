import SolitonClassification.FrozenKernelEndpoints
import SolitonClassification.FrozenShootingConsequences

namespace ClosedSimilarity.FrozenStress.Endpoint
open GlobalSupport Set Filter
open scoped Topology

/-- A true orbit of the frozen support equation whose transverse stress
    vanishes at both arclength ends. -/
theorem exists_symmetric_zero_scattering :
    ∃ c ∈ Ioo (-1/4 : ℝ) 1,
      Tendsto (seam c).rawI atTop (𝓝 0) ∧ Tendsto (seam c).rawI atBot (𝓝 0) ∧
      Tendsto (seam c).transverse atTop (𝓝 0) ∧ Tendsto (seam c).transverse atBot (𝓝 0) ∧
      ∀ s : ℝ, 12 ≤ -(seam c).radial s → ((seam c).transverse s)^2*(-(seam c).radial s) ≤ 128 :=
  realized_terminal_bounds.zero_scattering_orbit

/-- A whole interval of raw impacts is realized on each sufficiently high
    common incoming section, with no assumption on computed endpoint signs. -/
theorem all_high_sections_cover_impact_interval :
    ∃ S≥20, ∃ H₀ : ℝ, ∀ H≥H₀, ∃ w : SeamSection (-1/4) 1 S H,
      ∀ v ∈ Icc (-0.002:ℝ) 0.52, ∃ c : Icc (-1/4:ℝ) 1, (c:ℝ)∈Ioo (-1/4) 1 ∧
        seamImpact c (-w.time c) = v ∧ seamImpact c (w.time c) = v :=
  realized_terminal_bounds.all_high_sections

end ClosedSimilarity.FrozenStress.Endpoint
#print axioms ClosedSimilarity.FrozenStress.Endpoint.exists_symmetric_zero_scattering
#print axioms ClosedSimilarity.FrozenStress.Endpoint.all_high_sections_cover_impact_interval
