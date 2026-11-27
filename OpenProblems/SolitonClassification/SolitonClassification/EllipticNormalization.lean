import SolitonClassification.EllipticContinuation

noncomputable section
open Complex Filter Set Function
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- Only a nonreal period of the meromorphic germs is needed. Values assigned
to the extension at isolated singularities play no role. -/
theorem exists_normal_extension {k : ℝ → ℝ} {f : ℂ → ℂ} (hm : Meromorphic f)
    (ha : ∀t : ℝ, AnalyticAt ℂ f (t:ℂ)) (matchReal : ∀t : ℝ,f (t:ℂ)=(k t:ℂ))
    {v : ℂ} (vn : v.im≠0)
    (per : ∀x : ℂ,(fun z=>f (z+v)) =ᶠ[𝓝[≠] x] f) : Nonempty (EllipticExtension k) := by
  let g := toMeromorphicNFOn f univ
  have onU : MeromorphicOn f univ := hm.meromorphicOn
  have normal (z : ℂ) : MeromorphicNFAt g z := meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)
  have equal (z : ℂ) : g =ᶠ[𝓝[≠] z] f := onU.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have realEq (t : ℝ) : g =ᶠ[𝓝 (t:ℂ)] f :=
    ((normal _).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (ha t).meromorphicNFAt).mp (equal _)
  refine ⟨⟨g,normal,fun t=>(analyticAt_congr (realEq t)).mpr (ha t),
    fun t=>(realEq t).eq_of_nhds.trans (matchReal t),v,vn,?_⟩⟩
  intro x
  have tn : Tendsto (fun z : ℂ=>z+v) (𝓝[≠] x) (𝓝[≠] (x+v)) := by
    apply (continuous_id.add continuous_const).continuousWithinAt.tendsto_nhdsWithin
    intro u hu
    exact fun eq=>hu (add_right_cancel eq)
  have nf : MeromorphicNFAt (fun z=>g (z+v)) x :=
    meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (normal _)
  apply Filter.EventuallyEq.eq_of_nhds (f:=fun z=>g (z+v)) (g:=g) (x:=x)
  apply (nf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (normal x)).mp
  exact ((equal (x+v)).comp_tendsto tn).trans ((per x).trans (equal x).symm)

end ClosedSimilarity.MeromorphicCurvature

