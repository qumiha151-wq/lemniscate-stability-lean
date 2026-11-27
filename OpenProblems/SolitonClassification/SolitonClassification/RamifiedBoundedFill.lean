import SolitonClassification.RationalLocalJet
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open Complex Set Filter Function
open scoped Topology
namespace ClosedSimilarity.RamifiedBounded

/-- The values at the puncture are irrelevant to a holomorphic filling. -/
def Fills (f : ℂ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ f =ᶠ[𝓝[≠] 0] g

theorem fills_of_bounded {f : ℂ → ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z)
    (bounded : ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖ ≤ C) : Fills f := by
  obtain ⟨C,hC⟩ := bounded
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0:ℂ)) (fun z => ‖f z-f 0‖) := by
    refine ⟨C+‖f 0‖,?_⟩
    change ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z-f 0‖≤C+‖f 0‖
    filter_upwards [hC] with z hz using (norm_sub_le _ _).trans (by gcongr)
  have lim := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hb
  let g := update f 0 (limUnder (𝓝[≠] (0:ℂ)) f)
  have eq : f=ᶠ[𝓝[≠] (0:ℂ)] g := by
    filter_upwards [eventually_mem_nhdsWithin] with z nz
    exact (update_of_ne nz _ _).symm
  have cont : ContinuousAt g 0 := by
    rw [continuousAt_iff_punctured_nhds]
    simpa only [g,update_self] using lim.congr' eq
  exact ⟨g, Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    (by filter_upwards [hd,eventually_mem_nhdsWithin] with z dz nz
        apply dz.congr_of_eventuallyEq
        filter_upwards [isOpen_compl_singleton.mem_nhds nz] with x hx using update_of_ne hx _ _) cont, eq⟩

theorem Fills.meromorphic {f : ℂ→ℂ} (h : Fills f) : MeromorphicAt f 0 := by
  obtain ⟨g,hg,eq⟩ := h
  exact hg.meromorphicAt.congr eq.symm

/-- A meromorphic solution of a first-order linear ODE with fillable
coefficients has no pole. The equation need only hold off the puncture. -/
theorem linear_fills {f A B : ℂ→ℂ} (hm : MeromorphicAt f 0)
    (ha : Fills A) (hb : Fills B)
    (eq : deriv f =ᶠ[𝓝[≠] (0:ℂ)] fun z=>A z*f z+B z) : Fills f := by
  apply hm.meromorphicOrderAt_nonneg_iff.mp
  by_contra! neg
  cases ord : meromorphicOrderAt f 0 with
  | top => simp [ord] at neg
  | coe n =>
    have hn : n<0 := by simpa [ord] using neg
    obtain ⟨c,hc,j⟩ := RationalCurvature.Jet.of_order hm ord
    obtain ⟨A₀,hA,eA⟩ := ha
    obtain ⟨B₀,hB,eB⟩ := hb
    have p : RationalCurvature.Jet (fun z=>A z*f z) 0 n (A₀ 0*c) := by
      simpa using ((RationalCurvature.Jet.of_analytic hA).congr eA).mul j
    have q : RationalCurvature.Jet B 0 n 0 :=
      ((RationalCurvature.Jet.of_analytic hB).congr eB).weaken hn
    have bad := j.deriv.unique ((p.add q).weaken (m:=n-1) (by omega)) eq
    exact (mul_ne_zero (Int.cast_ne_zero.mpr (by omega)) hc) bad

theorem Fills.of_analytic {f : ℂ→ℂ} (h : AnalyticAt ℂ f 0) : Fills f :=
  ⟨f,h,EventuallyEq.rfl⟩

theorem Fills.congr {f g : ℂ→ℂ} (h : Fills f) (eq : g=ᶠ[𝓝[≠] (0:ℂ)] f) : Fills g := by
  obtain ⟨r,hr,er⟩ := h
  exact ⟨r,hr,eq.trans er⟩

theorem Fills.mul {f g : ℂ→ℂ} (hf : Fills f) (hg : Fills g) : Fills (fun z=>f z*g z) := by
  obtain ⟨u,hu,eu⟩ := hf
  obtain ⟨v,hv,ev⟩ := hg
  exact ⟨_,hu.mul hv,eu.mul ev⟩

theorem Fills.sub {f g : ℂ→ℂ} (hf : Fills f) (hg : Fills g) : Fills (fun z=>f z-g z) := by
  obtain ⟨u,hu,eu⟩ := hf
  obtain ⟨v,hv,ev⟩ := hg
  exact ⟨_,hu.sub hv,eu.sub ev⟩

theorem Fills.add {f g : ℂ→ℂ} (hf : Fills f) (hg : Fills g) : Fills (fun z=>f z+g z) := by
  obtain ⟨u,hu,eu⟩ := hf
  obtain ⟨v,hv,ev⟩ := hg
  exact ⟨_,hu.add hv,eu.add ev⟩

theorem Fills.pow {f : ℂ→ℂ} (hf : Fills f) (n:ℕ) : Fills (fun z=>f z^n) := by
  obtain ⟨u,hu,eu⟩ := hf
  exact ⟨_,hu.pow n,eu.mono (fun z h=>congrArg (·^n) h)⟩

theorem fills_const (c:ℂ) : Fills (fun _=>c) := Fills.of_analytic analyticAt_const

#print axioms fills_of_bounded
#print axioms linear_fills
end ClosedSimilarity.RamifiedBounded
