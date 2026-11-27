import SolitonClassification.RamifiedIsolatedContinuation
import SolitonClassification.RamifiedOrdinaryEnd

noncomputable section
open Complex Set Metric Filter
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RamifiedBounded RamifiedCurvature

/-- Meromorphic ordinary charts on the punctured power cover yield an
ordinary solution on the base. The missing value is removable or a
simple pole with residue ±3i, even when nearby chart poles were allowed. -/
theorem isolated_finite_cover_ordinary_end {q:ℕ} (hq:0<q) {a b:ℝ} (ha:0<a)
    (s₀:ℂ) (f:ℂ→ℂ) {r:ℝ} (hr:0<r)
    (charts : ∀w:ℂ,w≠0 → ‖w‖<r → ∃k:ℂ→ℂ,MeromorphicNFAt k (s₀+w^q) ∧
      (f=ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧
      ordinaryResidual a b k=ᶠ[𝓝[≠] (s₀+w^q)] fun _=>0) :
    ∃G:ℂ→ℂ,MeromorphicAt G s₀ ∧ (f=ᶠ[𝓝[≠] (0:ℂ)] fun w=>G (s₀+w^q)) ∧
      (∀ᶠ s in 𝓝[≠] s₀,AnalyticAt ℂ G s ∧ ordinaryResidual a b G s=0) ∧
      OrdinaryEnd a b s₀ G := by
  obtain ⟨G,mg,rep⟩:=isolated_finite_branch_descends hq ha s₀ f hr charts
  let P:=fun z:ℂ=>s₀+z^q
  have mg₀ : MeromorphicAt G (P 0) := by simpa [P,zero_pow hq.ne'] using mg
  have mp : MeromorphicAt (fun z=>G (s₀+z^q)) 0 :=
    mg₀.comp_analyticAt (g:=P) (by dsimp [P];fun_prop)
  have mf := mp.congr rep.symm
  obtain ⟨d,dp,near⟩:=Metric.mem_nhdsWithin_iff.mp mf.eventually_analyticAt
  have small : PuncturedCharts q (min r d) a b s₀ f := by
    intro w nw hw
    obtain ⟨k,_,eq,zero⟩:=charts w nw (lt_of_lt_of_le hw (min_le_left _ _))
    have wd : ‖w‖ < d := lt_of_lt_of_le hw (min_le_right _ _)
    have aw : AnalyticAt ℂ f w := near ⟨by simpa only [mem_ball,dist_zero_right] using wd,nw⟩
    have derivP : HasDerivAt P (speed q w) w := by simpa [P,speed] using ((hasDerivAt_pow q w).const_add s₀)
    have ap : AnalyticAt ℂ P w := by dsimp [P];fun_prop
    have da : AnalyticAt ℂ (k ∘ P) w := (analyticAt_congr eq).mp aw
    have ak : AnalyticAt ℂ k (s₀+w^q) := (analyticAt_comp_iff_of_deriv_ne_zero ap
      (derivP.deriv ▸ speed_ne hq nw)).mp da
    have az : AnalyticAt ℂ (ordinaryResidual a b k) (s₀+w^q) := by
      unfold ordinaryResidual ordinaryQuadratic ordinaryQuartic
      fun_prop (disch := assumption)
    have zf : AnalyticAt ℂ (fun _:ℂ=>(0:ℂ)) (s₀+w^q) := analyticAt_const
    exact ⟨k,ak,eq,((az.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE zf.continuousAt).mp zero).eq_of_nhds⟩
  have good:=descended_charts hq (lt_min hr dp) small rep
  exact ⟨G,mg,rep,good,ordinary_end_of_solution ha mg (good.mono (fun _ h=>h.2))⟩

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.isolated_finite_cover_ordinary_end
