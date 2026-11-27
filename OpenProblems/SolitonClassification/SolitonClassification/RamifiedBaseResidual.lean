import SolitonClassification.RamifiedFinitePrincipal
import SolitonClassification.RamifiedScalarContinuation

noncomputable section
open Complex Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace ClosedSimilarity.MeromorphicCurvature.Ramified
open RamifiedBounded RamifiedCurvature

/-- The disk has ordinary holomorphic charts everywhere off its central fiber. -/
def PuncturedCharts (q : ℕ) (r : ℝ) (a b s₀ : ℂ) (f : ℂ→ℂ) : Prop :=
  ∀w:ℂ,w≠0 → ‖w‖<r → ∃k:ℂ→ℂ, AnalyticAt ℂ k (s₀+w^q) ∧
    (f=ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0

theorem PuncturedCharts.eventual {q:ℕ} {r:ℝ} {a b s₀:ℂ} {f:ℂ→ℂ} (hr:0<r)
    (charts:PuncturedCharts q r a b s₀ f) :
    ∀ᶠ w in 𝓝[≠] (0:ℂ),∃k:ℂ→ℂ,AnalyticAt ℂ k (s₀+w^q) ∧
      (f=ᶠ[𝓝 w] fun z=>k (s₀+z^q)) ∧ ordinaryResidual a b k (s₀+w^q)=0 := by
  have near : ∀ᶠ w in 𝓝 (0:ℂ),‖w‖<r := by
    filter_upwards [ball_mem_nhds (0:ℂ) hr] with w small
    simpa only [mem_ball,dist_zero_right] using small
  filter_upwards [near.filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin] with w small nz
  exact charts w nz small

private theorem base_chart_at_lift {q:ℕ} (hq:0<q) {w s₀:ℂ} (nw:w≠0)
    {G k:ℂ→ℂ} (eq : (fun z=>G (s₀+z^q)) =ᶠ[𝓝 w] fun z=>k (s₀+z^q)) :
    G =ᶠ[𝓝 (s₀+w^q)] k := by
  let B := fun s:ℂ=>inverseSheet q w (s-s₀)
  have inside : w^q∈ball (w^q) (‖w^q‖/2) :=
    mem_ball_self (half_pos (norm_pos_iff.mpr (pow_ne_zero q nw)))
  have inv := (inverse_geometry hq nw inside).1
  have atc : AnalyticAt ℂ (inverseSheet q w) ((s₀+w^q)-s₀) := by simpa using inv
  have analytic : AnalyticAt ℂ B (s₀+w^q) :=
    atc.comp (f:=fun s:ℂ=>s-s₀) (analyticAt_id.sub analyticAt_const)
  have base : B (s₀+w^q)=w := by simp only [B,add_sub_cancel_left,inverse_center nw]
  have tend : Tendsto B (𝓝 (s₀+w^q)) (𝓝 w) := by simpa only [base] using analytic.continuousAt.tendsto
  filter_upwards [tend.eventually eq] with z h
  have proj : s₀+(B z)^q=z := by dsimp only [B];rw [inverse_power hq nw];ring
  simpa only [proj] using h

private theorem residual_core {a b x:ℂ} {G k:ℂ→ℂ} (eq:G=ᶠ[𝓝 x] k) :
    ordinaryResidual a b G x=ordinaryResidual a b k x := by
  simp only [ordinaryResidual,ordinaryQuadratic,ordinaryQuartic,eq.eq_of_nhds,
    eq.deriv.eq_of_nhds,eq.deriv.deriv.eq_of_nhds,eq.deriv.deriv.deriv.eq_of_nhds,
    eq.deriv.deriv.deriv.deriv.eq_of_nhds]

/-- Any representative produced by power descent satisfies the actual base
residual throughout a punctured neighborhood. -/
theorem descended_charts {q:ℕ} (hq:0<q) {r:ℝ} (hr:0<r) {a b s₀:ℂ} {G f:ℂ→ℂ}
    (charts:PuncturedCharts q r a b s₀ f)
    (agree:f=ᶠ[𝓝[≠] (0:ℂ)] fun w=>G (s₀+w^q)) :
    ∀ᶠ s in 𝓝[≠] s₀,AnalyticAt ℂ G s ∧ ordinaryResidual a b G s=0 := by
  have lift : ∀ᶠ w in 𝓝[≠] (0:ℂ),AnalyticAt ℂ G (s₀+w^q) ∧
      ordinaryResidual a b G (s₀+w^q)=0 := by
    filter_upwards [charts.eventual hr,eventually_eventually_nhdsWithin.mpr agree,
      eventually_mem_nhdsWithin] with w h same nw
    obtain ⟨k,ak,rep,law⟩:=h
    rw [isOpen_compl_singleton.nhdsWithin_eq nw] at same
    change f=ᶠ[𝓝 w] (fun z=>G (s₀+z^q)) at same
    have eq:=base_chart_at_lift hq nw (same.symm.trans rep)
    exact ⟨(analyticAt_congr eq).mpr ak,(residual_core eq).trans law⟩
  let ρ := fun s:ℂ=>rootSection q (s-s₀)
  have subz : Tendsto (fun s:ℂ=>s-s₀) (𝓝 s₀) (𝓝 0) := by
    have co : ContinuousAt (fun s:ℂ=>s-s₀) s₀ := by fun_prop
    simpa only [sub_self] using co.tendsto
  have tend : Tendsto ρ (𝓝[≠] s₀) (𝓝[≠] (0:ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨((root_tends_zero hq).comp subz).mono_left
      nhdsWithin_le_nhds,?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with z hz
    have rr:=root_pow hq (z-s₀)
    intro bad
    change rootSection q (z-s₀)=0 at bad
    rw [bad,zero_pow hq.ne'] at rr
    exact hz (sub_eq_zero.mp rr.symm)
  filter_upwards [tend.eventually lift] with z h
  have proj : s₀+(ρ z)^q=z := by dsimp only [ρ];rw [root_pow hq];ring
  simpa only [proj] using h

/-- Holomorphic scalar charts on all points of a punctured finite cover give
a meromorphic continuation solving the original equation in the base variable. -/
theorem finite_cover_base_solution {q:ℕ} (hq:0<q) {r:ℝ} (hr:0<r)
    (a b s₀:ℂ) (f:ℂ→ℂ) (charts:PuncturedCharts q r a b s₀ f) :
    ∃G:ℂ→ℂ,MeromorphicAt G s₀ ∧ (f=ᶠ[𝓝[≠] (0:ℂ)] fun w=>G (s₀+w^q)) ∧
      ∀ᶠ s in 𝓝[≠] s₀,AnalyticAt ℂ G s ∧ ordinaryResidual a b G s=0 := by
  have mf := (finite_principal_of_charts hq hr a b s₀ f charts).2
  have deck := finite_meromorphic_deck_of_ordinary_charts hq a b s₀ mf (charts.eventual hr)
  obtain ⟨G,mg,rep⟩:=descends_power_cover hq mf deck s₀
  exact ⟨G,mg,rep,descended_charts hq hr charts rep⟩

end ClosedSimilarity.MeromorphicCurvature.Ramified
#print axioms ClosedSimilarity.MeromorphicCurvature.Ramified.finite_cover_base_solution
