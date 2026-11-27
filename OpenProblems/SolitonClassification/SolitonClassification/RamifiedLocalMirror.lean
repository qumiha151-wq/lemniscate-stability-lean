import SolitonClassification.MeromorphicPoleParity
import SolitonClassification.MeromorphicPoleIndicial
import SolitonClassification.RamifiedPuncturedIdentity

noncomputable section
open Complex Set Filter
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded
open MeromorphicCurvature RationalCurvature

/-- The ordinary pole calculation is local in complex arclength. -/
theorem ordinary_pole_odd_germ {a b:ℝ} (ap:0<a) {k:ℂ→ℂ} {x:ℂ}
    (nf:MeromorphicNFAt k x) (sing:¬AnalyticAt ℂ k x)
    (law:ordinaryResidual a b k=ᶠ[𝓝[≠] x] fun _=>0) : k=ᶠ[𝓝 x] oddReflect x k := by
  have neg : meromorphicOrderAt k x<0 :=
    lt_of_not_ge (fun ge=>sing (nf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ge))
  lift meromorphicOrderAt k x to ℤ using LT.lt.ne_top neg with n hn
  obtain ⟨_,c,cs,jet,⟨R,ar,expan⟩,_⟩ := pole_expansion ap nf.meromorphicAt hn.symm
    (WithTop.coe_lt_zero.mp neg) law
  have rg : ordinaryResidual a b (oddReflect x k)=ᶠ[𝓝[≠] x] fun _=>0 := by
    filter_upwards [(reflect_punctured x).eventually law] with z hz
    exact (residual_oddReflect _ _ _ _ _).trans hz
  have rn : MeromorphicNFAt (oddReflect x k) x := by
    have nx : MeromorphicNFAt k (reflect x x) := by simpa [reflect,two_mul] using nf
    exact neg_normal (nx.comp_analyticAt (g:=reflect x) (analyticAt_const.sub analyticAt_id))
  apply (nf.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds rn).mp
  apply reflection_of_fifth_uniqueness (regular_difference_of_remainder ar expan)
  intro m d nonneg dn j
  exact pole_difference_order_five jet (jet_odd_simple jet) cs j dn nonneg law rg

#print axioms ordinary_pole_odd_germ
end ClosedSimilarity.RamifiedBounded
