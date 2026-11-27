import SolitonClassification.RamifiedDerivative

noncomputable section
open Complex Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified

theorem ds_of_branch_germ {q : ℕ} (hq : 0<q) {F k : ℂ→ℂ} {s₀ w : ℂ} (nw : w≠0)
    (ak : AnalyticAt ℂ k (s₀+w^q))
    (rep : F =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) :
    ds q F =ᶠ[𝓝 w] fun z=>deriv k (s₀+z^q) := by
  have continuous : Continuous (fun z:ℂ=>s₀+z^q) := by fun_prop
  have nearby := continuous.continuousAt.tendsto.eventually ak.eventually_analyticAt
  filter_upwards [rep.eventuallyEq_nhds,nearby,eventually_ne_nhds nw] with z h hz nz
  change ((q:ℂ)*z^(q-1))⁻¹*deriv F z=_
  rw [h.deriv_eq]
  exact ds_branch hq nz hz.differentiableAt

/-- The ordinary residual at a regular point pulls back to the displayed
ramified residual for a genuine locally represented branch, through order four. -/
theorem residual_of_branch_germ {q : ℕ} (hq : 0<q) (a b : ℂ) {F k : ℂ→ℂ} {s₀ w : ℂ}
    (nw : w≠0) (ak : AnalyticAt ℂ k (s₀+w^q))
    (rep : F =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) :
    jetResidual q a b F w = ordinaryResidual a b k (s₀+w^q) := by
  have d1 := ds_of_branch_germ hq nw ak rep
  have d2 := ds_of_branch_germ hq nw ak.deriv d1
  have d3 := ds_of_branch_germ hq nw ak.deriv.deriv d2
  have d4 := ds_of_branch_germ hq nw ak.deriv.deriv.deriv d3
  simp only [jetResidual,ordinaryResidual,ordinaryQuadratic,ordinaryQuartic,rep.eq_of_nhds,
    d1.eq_of_nhds,d2.eq_of_nhds,d3.eq_of_nhds,d4.eq_of_nhds]

/-- Each ordinary germ can vary with the sheet point. -/
theorem residual_on_puncture {q : ℕ} (hq : 0<q) (a b s₀ : ℂ) {F : ℂ→ℂ}
    (charts : ∀ᶠ w in 𝓝[≠] (0:ℂ), ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+w^q) ∧
      (F =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0) :
    jetResidual q a b F =ᶠ[𝓝[≠] 0] fun _=>0 := by
  filter_upwards [charts,eventually_mem_nhdsWithin] with w h nw
  obtain ⟨k,ak,rep,zero⟩ := h
  exact (residual_of_branch_germ hq a b nw ak rep).trans zero

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.residual_on_puncture
