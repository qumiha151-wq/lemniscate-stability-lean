import SolitonClassification.RamifiedPowerDescent

noncomputable section
open Complex Polynomial Filter Set Function
open scoped Topology Polynomial
namespace ClosedSimilarity.RamifiedCurvature

theorem agrees_with_root_section {q : ℕ} (hq : 0<q) {f : ℂ → ℂ}
    (invar : ∀ζ : ℂ,ζ^q=1 → (fun w=>f (ζ*w)) =ᶠ[𝓝[≠] (0:ℂ)] f) :
    (fun w=>f (rootSection q (w^q))) =ᶠ[𝓝 (0:ℂ)] f := by
  let F (z : ℂ) := f (rootSection q z)
  have fin : {ζ : ℂ | ζ^q=1}.Finite := by
    have hn := Polynomial.finite_setOfPred_isRoot (X_pow_sub_C_ne_zero hq (1:ℂ))
    simpa [Polynomial.IsRoot.def,sub_eq_zero] using hn
  have all : ∀ᶠ w in 𝓝[≠] (0:ℂ),∀ζ∈{z : ℂ | z^q=1},f (ζ*w)=f w :=
    fin.eventually_all.mpr invar
  have germ : (fun w=>F (w^q)) =ᶠ[𝓝[≠] (0:ℂ)] f := by
    filter_upwards [all,eventually_mem_nhdsWithin] with w hw wn
    have nz : w≠0 := wn
    let ζ := rootSection q (w^q)/w
    have cond : ζ^q=1 := by dsimp [ζ];rw [div_pow,root_pow hq,div_self (pow_ne_zero _ nz)]
    have eq:=hw ζ cond
    simpa only [ζ,div_mul_cancel₀ _ nz] using eq
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE germ (by simp [zero_pow hq.ne',root_at_zero hq])

/-- A singularity that is meromorphic on a finite power cover descends
whenever its punctured germ is invariant under each deck rotation. -/
theorem descends_power_cover {q : ℕ} (hq : 0<q) {f : ℂ → ℂ} (mer : MeromorphicAt f 0)
    (invar : ∀ζ : ℂ,ζ^q=1 → (fun w=>f (ζ*w)) =ᶠ[𝓝[≠] (0:ℂ)] f) (s₀ : ℂ) :
    ∃G : ℂ → ℂ, MeromorphicAt G s₀ ∧
      f =ᶠ[𝓝[≠] (0:ℂ)] (fun w=>G (s₀+w^q)) := by
  let F (z : ℂ) := f (rootSection q z)
  have germ : (fun z=>F (z^q)) =ᶠ[𝓝[≠] (0:ℂ)] f :=
    (agrees_with_root_section hq invar).filter_mono nhdsWithin_le_nhds
  have main := meromorphicAt_of_comp_pow hq (mer.congr germ.symm)
  refine ⟨fun z=>F (z-s₀),?_,?_⟩
  · apply meromorphicAt_fun_comp_sub_const_iff_meromorphicAt.mpr
    simpa only [sub_self] using main
  · simpa only [add_sub_cancel_left] using germ.symm

theorem analytic_descends_power_cover {q : ℕ} (hq : 0<q) {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (invar : ∀ζ : ℂ,ζ^q=1 → (fun w=>f (ζ*w)) =ᶠ[𝓝[≠] (0:ℂ)] f) (s₀ : ℂ) :
    ∃G : ℂ → ℂ, AnalyticAt ℂ G s₀ ∧ f =ᶠ[𝓝 (0:ℂ)] (fun w=>G (s₀+w^q)) := by
  let F (z : ℂ) := f (rootSection q z)
  have germ : (fun w=>F (w^q)) =ᶠ[𝓝 (0:ℂ)] f := agrees_with_root_section hq invar
  have main := analyticAt_of_comp_pow hq ((analyticAt_congr germ).mpr ha)
  have center : AnalyticAt ℂ F (s₀-s₀) := by simpa using main
  refine ⟨fun z=>F (z-s₀),center.comp (f:=fun z:ℂ=>z-s₀) (analyticAt_id.sub analyticAt_const),?_⟩
  simpa only [add_sub_cancel_left] using germ.symm

end ClosedSimilarity.RamifiedCurvature
#print axioms ClosedSimilarity.RamifiedCurvature.descends_power_cover

