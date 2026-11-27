import SolitonClassification.RamifiedPoleFilling
import SolitonClassification.RamifiedFinitePrincipal
import SolitonClassification.RamifiedScalarContinuation

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Complex Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded
open MeromorphicCurvature RamifiedCurvature

/-- Every physical scalar branch on a finite cyclic cover of a punctured
disk admits a meromorphic descent at its missing base value. The ordinary
charts may have poles accumulating toward the missing point, and no size
bound is assumed. -/
theorem isolated_finite_branch_descends {q:ℕ} (hq:0<q) {a b:ℝ} (ap:0<a)
    (s₀:ℂ) (f:ℂ→ℂ) {r:ℝ} (hr:0<r)
    (charts : ∀w:ℂ,w≠0 → ‖w‖<r → ∃k:ℂ→ℂ, MeromorphicNFAt k (s₀+w^q) ∧
        (f=ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧
        ordinaryResidual a b k=ᶠ[𝓝[≠] (s₀+w^q)] fun _=>0) :
    ∃G:ℂ→ℂ,MeromorphicAt G s₀ ∧ f=ᶠ[𝓝[≠] 0] fun w=>G (s₀+w^q) := by
  let R:=r/5
  have Rp : 0<R := by dsimp [R];positivity
  have Rr : R<r := by dsimp [R];linarith
  have nf (w:ℂ) (nw:w≠0) (hw:‖w‖<r) : MeromorphicNFAt f w := by
    obtain ⟨k,mk,eq,-⟩ := charts w nw hw
    exact (meromorphicNFAt_congr eq).mpr (mk.comp_analyticAt (g:=fun z:ℂ=>s₀+z^q) (by fun_prop))
  by_cases all : ∀w:ℂ,w≠0 → ‖w‖<R → AnalyticAt ℂ f w
  · have ordinary (w:ℂ) (nw:w≠0) (hw:‖w‖<R) : ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+w^q) ∧
        (f=ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0 := by
      obtain ⟨k,_,eq,zero⟩ := charts w nw (hw.trans Rr)
      let P (z:ℂ) := s₀+z^q
      have dp : HasDerivAt P (speed q w) w := by simpa [P,speed] using ((hasDerivAt_pow q w).const_add s₀)
      have pa : AnalyticAt ℂ P w := by dsimp [P];fun_prop
      have da : AnalyticAt ℂ (k ∘ P) w := (analyticAt_congr eq).mp (all w nw hw)
      have an : AnalyticAt ℂ k (s₀+w^q) := (analyticAt_comp_iff_of_deriv_ne_zero pa
        (dp.deriv ▸ speed_ne hq nw)).mp da
      have az : AnalyticAt ℂ (ordinaryResidual a b k) (s₀+w^q) := by
        unfold ordinaryResidual ordinaryQuadratic ordinaryQuartic
        fun_prop (disch := assumption)
      have zf : AnalyticAt ℂ (fun _:ℂ=>(0:ℂ)) (s₀+w^q) := analyticAt_const
      exact ⟨k,an,eq,((az.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE zf.continuousAt).mp zero).eq_of_nhds⟩
    have mer := (finite_principal_of_charts hq Rp a b s₀ f ordinary).2
    apply descends_power_cover hq mer _ s₀
    apply MeromorphicCurvature.Ramified.finite_meromorphic_deck_of_ordinary_charts hq a b s₀ mer
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds (0:ℂ) Rp),
      eventually_mem_nhdsWithin] with w hw nw
    exact ordinary w nw (by simpa only [mem_ball,dist_zero_right] using hw)
  · push Not at all
    obtain ⟨p,np,sz,sing⟩ := all
    obtain ⟨k,mk,eq,law⟩ := charts p np (sz.trans Rr)
    apply descends_of_nearby_pole hq np (show 4*‖p‖≤r by dsimp [R] at sz;linarith only [sz,hr]) nf ap k mk _ eq law
    intro an
    exact sing ((analyticAt_congr eq).mpr (an.comp (f:=fun z:ℂ=>s₀+z^q) (by fun_prop)))

#print axioms isolated_finite_branch_descends
end ClosedSimilarity.RamifiedBounded
