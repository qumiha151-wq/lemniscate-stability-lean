import SolitonClassification.MeromorphicMaximalDomain

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature

/-- A normalized meromorphic germ is normalized throughout some neighborhood. -/
theorem normal_nearby {g : ℂ→ℂ} {x : ℂ} (nf : MeromorphicNFAt g x) :
    ∀ᶠ y in 𝓝 x,MeromorphicNFAt g y := by
  filter_upwards [eventually_nhdsWithin_iff.mp nf.meromorphicAt.eventually_analyticAt] with y hy
  by_cases eq : y=x
  · simpa only [eq] using nf
  · exact (hy eq).meromorphicNFAt

theorem fill_bad_subset {S : Set ℂ} (closed : IsClosed S) {f : ℂ→ℂ}
    (nf : ∀x∉S,MeromorphicNFAt f x) : (fillDomain S f)ᶜ ⊆ S := by
  intro x hx
  by_contra no
  exact hx ⟨f,original_fills closed nf no⟩

/-- The isolated-point property of closed countable sets removes all exceptional
points once the differential equation repairs isolated holes. -/
theorem all_filled_of_isolated_repair {S : Set ℂ} (closed : IsClosed S) (sC : S.Countable)
    {f : ℂ→ℂ} (nf : ∀x∉S,MeromorphicNFAt f x)
    (repair : ∀x, x∉fillDomain S f → (∀ᶠ y in 𝓝[≠] x,y∈fillDomain S f) →
      MeromorphicAt (maximalFill S f) x) : ∀x,x∈fillDomain S f := by
  by_contra! bad
  have sub:=fill_bad_subset closed nf
  obtain ⟨x,hx,isol⟩:=countable_closed_isolated (fillDomain_open S f).isClosed_compl
    (sC.mono sub) (show (fillDomain S f)ᶜ.Nonempty from bad)
  have reg:=repair x hx (by simpa using isol)
  let g:=toMeromorphicNFAt (maximalFill S f) x
  have gn : MeromorphicNFAt g x := meromorphicNFAt_toMeromorphicNFAt
  apply hx
  refine ⟨g,normal_nearby gn,Eventually.of_forall (fun y hy=>?_)⟩
  have neq : y≠x := fun eq=>hy (eq ▸ sub hx)
  have hs:=reg.eqOn_compl_singleton_toMeromorphicNFAt (show y∈{x}ᶜ from neq)
  exact hs.symm.trans ((original_fills closed nf hy).maximal_germ sC).eq_of_nhds

end ClosedSimilarity.MeromorphicCurvature

