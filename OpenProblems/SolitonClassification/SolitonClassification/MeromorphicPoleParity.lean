import SolitonClassification.MeromorphicPoleMirror

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature
open RationalCurvature

/-- Odd order is incompatible with a nonzero even Laurent germ. -/
theorem even_difference_fifth_impossible {x c : ℂ} {D : ℂ → ℂ} (jet : Jet D x 5 c)
    (even : ∀z,D (reflect x z)=D z) (nc : c≠0) : False := by
  have e := (jet_pull jet).unique jet (Eventually.of_forall even)
  norm_num at e
  exact nc (by linear_combination -e/2)

/-- The simple polar parts of k(s) and -k(2x-s) cancel in their difference.
The displayed analytic representative also handles points where the original
complex-valued function has an arbitrary assigned value at its pole. -/
theorem regular_difference_of_remainder {x c : ℂ} {f R : ℂ → ℂ}
    (ar : AnalyticAt ℂ R x)
    (expan : f =ᶠ[𝓝[≠] x] fun z=>c/(z-x)+(z-x)^3*R z) :
    ∃D : ℂ → ℂ, AnalyticAt ℂ D x ∧
      (fun z=>f z-oddReflect x f z) =ᶠ[𝓝[≠] x] D := by
  have inner : AnalyticAt ℂ (reflect x) x := analyticAt_const.sub analyticAt_id
  have reflected : AnalyticAt ℂ R (reflect x x) := by simpa using ar
  refine ⟨fun z=>(z-x)^3*(R z-R (reflect x z)),
    ((analyticAt_id.sub analyticAt_const).pow 3).mul (ar.sub (reflected.comp (f:=reflect x) inner)),?_⟩
  filter_upwards [expan,(reflect_punctured x).eventually expan] with z hz hzr
  change f (reflect x z)=c/(reflect x z-x)+(reflect x z-x)^3*R (reflect x z) at hzr
  dsimp only [oddReflect]
  rw [hz,hzr,reflect_sub,div_neg]
  ring

/-- A reflected meromorphic pole agrees with its signed reflection
whenever fifth order is the only possible nonzero regular difference. -/
theorem reflection_of_fifth_uniqueness {x : ℂ} {f : ℂ → ℂ}
    (analytic : ∃D : ℂ → ℂ, AnalyticAt ℂ D x ∧
      (fun z=>f z-oddReflect x f z) =ᶠ[𝓝[≠] x] D)
    (orderFive : ∀ (m : ℤ) (d : ℂ), 0≤m → d≠0 →
      Jet (fun z=>f z-oddReflect x f z) x m d → m=5) :
    f =ᶠ[𝓝[≠] x] oddReflect x f := by
  obtain ⟨D,ad,eq⟩ := analytic
  by_cases top : meromorphicOrderAt D x=⊤
  · have van := meromorphicOrderAt_eq_top_iff.mp top
    filter_upwards [eq,van] with z he hv
    exact sub_eq_zero.mp (he.trans hv)
  · lift meromorphicOrderAt D x to ℤ using top with m hm
    have nonneg : (0:WithTop ℤ)≤m := hm ▸ ad.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr ad
    obtain ⟨d,dn,j⟩ := Jet.of_order ad.meromorphicAt hm.symm
    have j' := j.congr eq
    have five := orderFive m d (WithTop.coe_nonneg.mp nonneg) dn j'
    subst m
    exact False.elim (even_difference_fifth_impossible j' (fun z=>by
      simp only [oddReflect,reflect_twice];ring) dn)

end ClosedSimilarity.MeromorphicCurvature

