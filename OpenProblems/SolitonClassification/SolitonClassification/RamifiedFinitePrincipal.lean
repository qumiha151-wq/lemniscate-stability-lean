import SolitonClassification.RamifiedDiskEstimate
import SolitonClassification.RamifiedBoundedCurvature
import SolitonClassification.RamifiedLiftDisk
import SolitonClassification.RamifiedDeckDescent

noncomputable section
open Complex Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded
open MeromorphicCurvature RamifiedCurvature

/-- Ordinary solution germs on the sheets of a punctured finite cover
already imply finite principal part in its uniformizer. -/
theorem finite_principal_of_charts {q:ℕ} (hq:0<q) {r:ℝ} (hr:0<r) (a b s₀:ℂ) (f:ℂ→ℂ)
    (charts : ∀v:ℂ,v≠0 → ‖v‖<r → ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+v^q) ∧
      (f=ᶠ[𝓝 v] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+v^q)=0) :
    Fills (fun w=>w^q*f w) ∧ MeromorphicAt f 0 := by
  have small : ∀ᶠ w in 𝓝 (0:ℂ), ‖w‖<r/2 := by
    filter_upwards [ball_mem_nhds (0:ℂ) (half_pos hr)] with z hz
    simpa only [mem_ball,dist_zero_right] using hz
  have rad : ∀ᶠ w in 𝓝 (0:ℂ), ‖w^q‖<2 := by
    have lim := (continuous_pow q (M:=ℂ)).continuousAt (x:=0)
    have nlim : Tendsto (fun z:ℂ=>‖z^q‖) (𝓝 0) (𝓝 0) := by
      simpa only [zero_pow hq.ne',norm_zero] using! lim.norm.tendsto
    exact nlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<2))
  have dh : ∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ (fun z=>z^q*f z) w := by
    filter_upwards [small.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with w hw nw
    obtain ⟨k,ak,eq,-⟩ := charts w nw (by linarith only [hw,hr])
    have af : AnalyticAt ℂ f w := (analyticAt_congr eq).mpr (ak.comp (f:=fun z:ℂ=>s₀+z^q) (by fun_prop))
    exact ((analyticAt_id.pow q).mul af).differentiableAt
  have fb : ∀ᶠ w in 𝓝[≠] (0:ℂ), ‖w^q*f w‖≤2*diskConstant a b := by
    filter_upwards [small.filter_mono nhdsWithin_le_nhds,rad.filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with w hw wr nw
    have sz : 2*‖w‖≤r := by linarith only [hw]
    obtain ⟨K,center,solution⟩ := ordinary_on_lift_disk hq nw sz a b s₀ f charts
    have db := disk_curvature_bound (half_pos (norm_pos_iff.mpr (pow_ne_zero q nw)))
      (show ‖w^q‖/2≤1 by linarith only [wr])
      (fun t ht=>(solution t ht).1) (fun t ht=>(solution t ht).2)
    rw [center] at db
    rw [norm_mul]
    linarith only [db]
  have fill := fills_of_bounded dh ⟨2*diskConstant a b,fb⟩
  refine ⟨fill,(fill.meromorphic.div ((analyticAt_id.pow q).meromorphicAt)).congr ?_⟩
  filter_upwards [eventually_mem_nhdsWithin] with w nw
  change w^q*f w/w^q=f w
  field_simp [pow_ne_zero q nw]

/-- A bounded solution of the true pulled-back support system descends to a
holomorphic germ in the original arclength variable. -/
theorem bounded_curvature_descends {q:ℕ} (hq:0<q) {a b:ℂ} {k v F h:ℂ→ℂ}
    (bound : ∃ C:ℝ,∀ᶠ w in 𝓝[≠] (0:ℂ),‖k w‖≤C)
    (law : ∀ᶠ w in 𝓝[≠] (0:ℂ),Laws q a b k v F h w) (s₀:ℂ) :
    ∃K:ℂ→ℂ,AnalyticAt ℂ K s₀ ∧ k=ᶠ[𝓝[≠] 0] fun z=>K (s₀+z^q) := by
  obtain ⟨K,ak,eq,deck⟩ := bounded_curvature_deck hq bound law
  obtain ⟨G,ag,eg⟩ := analytic_descends_power_cover hq ak
    (fun η he=>(deck η he).filter_mono nhdsWithin_le_nhds) s₀
  exact ⟨G,ag,eq.trans (eg.filter_mono nhdsWithin_le_nhds)⟩

#print axioms finite_principal_of_charts
#print axioms bounded_curvature_descends
end ClosedSimilarity.RamifiedBounded
