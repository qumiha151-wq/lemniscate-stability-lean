import SolitonClassification.MeromorphicBoundaryRemoval
import SolitonClassification.MeromorphicScalarEquation

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- Propagate the physical scalar equation from real arclength throughout the
maximal normalized domain. Its complement is countable and cannot disconnect the plane. -/
theorem residual_on_fillDomain {a b L : ℝ} (p : PeriodicSupportProfile a b L)
    {S : Set ℂ} (closed : IsClosed S) (sC : S.Countable) (regular : ∀t : ℝ,(t:ℂ)∉S)
    {f : ℂ→ℂ} (nf : ∀x∉S,MeromorphicNFAt f x) (an : ∀t : ℝ,AnalyticAt ℂ f (t:ℂ))
    (rep : ∀t : ℝ,f (t:ℂ)=(p.k t:ℂ)) {z : ℂ} (hz : z∈fillDomain S f) :
    ordinaryResidual a b (maximalFill S f) =ᶠ[𝓝[≠] z] fun _=>0 := by
  let H:=maximalFill S f
  have germs (t : ℝ) : H =ᶠ[𝓝 (t:ℂ)] f := (original_fills closed nf (regular t)).maximal_germ sC
  have useReal (t : ℝ) : ordinaryResidual a b H (t:ℂ)=0 :=
    residual_on_real_trace p (fun u=>(analyticAt_congr (germs u)).mpr (an u))
      (fun u=>(germs u).eq_of_nhds.trans (rep u)) t
  have mer (x : ℂ) (hx : x∈fillDomain S f) : MeromorphicAt (ordinaryResidual a b H) x :=
    meromorphicAt_ordinaryResidual (maximal_normal sC hx).meromorphicAt a b
  have zReal : (0:ℂ)∉S := by simpa using regular 0
  have base : (0:ℂ)∈fillDomain S f := ⟨f,original_fills closed nf zReal⟩
  have conn : IsPreconnected (fillDomain S f) := by
    simpa using countable_complement_connected (sC.mono (fill_bad_subset closed nf))
  apply identity_connected_germs conn mer (fun _ _=>analyticAt_const.meromorphicAt) base _ hz
  apply ((mer 0 base).frequently_zero_iff_eventuallyEq_zero).mp
  have tends : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro t ht
    simpa using ht
  by_contra! no
  obtain ⟨t,nt⟩:=(tends.eventually no).exists
  exact nt (useReal t)

end ClosedSimilarity.MeromorphicCurvature

