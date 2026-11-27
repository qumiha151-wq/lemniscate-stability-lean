import SolitonClassification.RamifiedRegularStress
import SolitonClassification.RamifiedPhysicalPole

noncomputable section
open Complex Filter Set
open scoped Topology
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RamifiedBounded RationalCurvature

/-- A bounded branch of ordinary analytic scalar curvature charts has a
holomorphic filling invariant under every deck rotation. -/
theorem bounded_deck_of_scalar_charts {q:ℕ} (hq:0<q) (a b s₀:ℂ) {f:ℂ→ℂ}
    (charts : ∀ᶠ w in 𝓝[≠] (0:ℂ), ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+w^q) ∧
      (f =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0)
    (bound : ∃C:ℝ,∀ᶠ w in 𝓝[≠] (0:ℂ),‖f w‖≤C) :
    ∃K:ℂ→ℂ,AnalyticAt ℂ K 0 ∧ f=ᶠ[𝓝[≠] 0] K ∧
      ∀r:ℂ,r^q=1 → (fun z=>K (r*z))=ᶠ[𝓝 0] K := by
  have diff : ∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ f w := by
    filter_upwards [charts] with w h
    obtain ⟨k,ak,rep,-⟩:=h
    have dp : DifferentiableAt ℂ (fun z:ℂ=>s₀+z^q) w := by fun_prop
    exact (ak.differentiableAt.comp w dp).congr_of_eventuallyEq rep
  obtain ⟨G,ag,eq⟩:=fills_of_bounded diff bound
  rcases ag.eventually_eq_zero_or_eventually_ne_zero with vanish|reg
  · exact ⟨fun _=>0,analyticAt_const,eq.trans (vanish.filter_mono nhdsWithin_le_nhds),
      fun _ _=>EventuallyEq.rfl⟩
  · have nz : ∀ᶠ w in 𝓝[≠] (0:ℂ),f w≠0 := by
      filter_upwards [eq,reg] with w h ne
      rwa [h]
    exact bounded_curvature_deck hq bound (laws_of_scalar_charts hq a b s₀ charts nz)

/-- At a meromorphic point on a finite cover, the ordinary scalar charts
already force deck invariance, including the identically zero case. -/
theorem finite_meromorphic_deck_of_ordinary_charts {q:ℕ} (hq:0<q) (a b s₀:ℂ) {f:ℂ→ℂ}
    (mf : MeromorphicAt f 0)
    (charts : ∀ᶠ w in 𝓝[≠] (0:ℂ), ∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+w^q) ∧
      (f =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0) :
    ∀r:ℂ,r^q=1 → (fun w=>f (r*w)) =ᶠ[𝓝[≠] (0:ℂ)] f := by
  intro r hr
  have rn : r≠0 := by intro z;rw [z,zero_pow (Nat.ne_of_gt hq)] at hr;norm_num at hr
  by_cases top : meromorphicOrderAt f 0=⊤
  · have vanish := meromorphicOrderAt_eq_top_iff.mp top
    filter_upwards [(deck_punctured rn).eventually vanish,vanish] with w a₁ a₂
    exact a₁.trans a₂.symm
  lift meromorphicOrderAt f 0 to ℤ using top with n order
  by_cases pole : n<0
  · exact finite_pole_deck_of_ordinary_charts hq a b s₀ mf order.symm pole charts r hr
  obtain ⟨c,_,p,ap,_,rep⟩:=Jet.of_order mf order.symm
  let A := fun z:ℂ=>(z-0)^n.toNat*p z
  have aA : AnalyticAt ℂ A 0 := ((analyticAt_id.sub analyticAt_const).pow _).mul ap
  have eA : f=ᶠ[𝓝[≠] (0:ℂ)] A := by
    rw [show n=(n.toNat:ℤ) from (Int.toNat_of_nonneg (by omega)).symm] at rep
    simpa only [A,zpow_natCast] using rep
  have bound : ∃C:ℝ,∀ᶠ z in 𝓝[≠] (0:ℂ),‖f z‖≤C := by
    refine ⟨‖A 0‖+1,?_⟩
    have near := aA.continuousAt.norm.eventually_lt_const (show ‖A 0‖<‖A 0‖+1 by linarith)
    filter_upwards [eA,near.filter_mono nhdsWithin_le_nhds] with z e v
    exact e ▸ v.le
  obtain ⟨K,_,agree,allr⟩:=bounded_deck_of_scalar_charts hq a b s₀ charts bound
  filter_upwards [(deck_punctured rn).eventually agree,(allr r hr).filter_mono nhdsWithin_le_nhds,agree]
    with w a₁ a₂ a₃
  exact a₁.trans (a₂.trans a₃.symm)

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.finite_meromorphic_deck_of_ordinary_charts
