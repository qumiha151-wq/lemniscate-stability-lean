import SolitonClassification.CountableTraceEquation
import SolitonClassification.RamifiedIsolatedContinuation

noncomputable section
open Complex Filter Set Metric
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- A single-valued meromorphic solution of the physical scalar equation fills
an isolated puncture, allowing ordinary poles to accumulate towards it. -/
theorem ordinary_isolated_repair {a b : ℝ} (ap : 0<a) {H : ℂ→ℂ} (x : ℂ)
    (punct : ∀ᶠ y in 𝓝[≠] x,MeromorphicNFAt H y ∧
      ordinaryResidual a b H =ᶠ[𝓝[≠] y] fun _=>0) : MeromorphicAt H x := by
  obtain ⟨r,hr,within⟩:=Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp punct)
  let F:=fun w:ℂ=>H (x+w)
  obtain ⟨G,mg,rep⟩:=RamifiedBounded.isolated_finite_branch_descends (q:=1) (by decide)
    (b:=b) ap x F hr (by
      intro w nw hw
      have radius : dist (x+w) x<r := by simpa [dist_eq_norm] using hw
      have ne : x+w≠x := by simpa using nw
      obtain ⟨normal,law⟩:=within radius ne
      exact ⟨H,by simpa using normal,by simp [F],by simpa using law⟩)
  have tends : Tendsto (fun z:ℂ=>z-x) (𝓝[≠] x) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,eventually_mem_nhdsWithin.mono (fun _ hn=>sub_ne_zero.mpr hn)⟩
    have ct : Tendsto (fun z:ℂ=>z-x) (𝓝 x) (𝓝 (x-x)) :=
      (show ContinuousAt (fun z:ℂ=>z-x) x from by fun_prop)
    simpa only [sub_self] using ct.mono_left (show 𝓝[≠] x≤𝓝 x from nhdsWithin_le_nhds)
  have same : H =ᶠ[𝓝[≠] x] G := by
    filter_upwards [tends.eventually rep] with y hy
    simpa [F] using hy
  exact (MeromorphicAt.meromorphicAt_congr same).mpr mg

end ClosedSimilarity.MeromorphicCurvature

