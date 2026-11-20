import Migration.SeparatedEndpointEnergy
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-! The vertical height interval of the curve is determined by the actual
position on one period. Immersion and closure make its width positive. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def bottom (t : ℝ) : ℝ := sInf ((fun u => (c.position t u).im) '' Icc 0 c.period)
def top (t : ℝ) : ℝ := sSup ((fun u => (c.position t u).im) '' Icc 0 c.period)
def verticalWidth (t : ℝ) : ℝ := c.top t-c.bottom t

theorem height_range_of_slice_continuous {t : ℝ} (hpc : Continuous (c.position t)) :
    c.HasHeightRange Complex.imCLM t (c.bottom t) (c.top t) := by
  let f := fun u => (c.position t u).im
  have hf : Continuous f := Complex.continuous_im.comp hpc
  have hne : (Icc 0 c.period).Nonempty := ⟨0,le_rfl,c.period_pos.le⟩
  obtain ⟨u,hu,hmin⟩ := isCompact_Icc.exists_isMinOn hne hf.continuousOn
  obtain ⟨v,hv,hmax⟩ := isCompact_Icc.exists_isMaxOn hne hf.continuousOn
  have hbot : c.bottom t=f u :=
    (show IsLeast (f '' Icc 0 c.period) (f u) from
      ⟨⟨u,hu,rfl⟩,by rintro _ ⟨x,hx,rfl⟩; exact hmin hx⟩).csInf_eq
  have htop : c.top t=f v :=
    (show IsGreatest (f '' Icc 0 c.period) (f v) from
      ⟨⟨v,hv,rfl⟩,by rintro _ ⟨x,hx,rfl⟩; exact hmax hx⟩).csSup_eq
  rw [hbot,htop]
  exact ⟨fun x hx => ⟨hmin hx,hmax hx⟩, ⟨u,hu,rfl⟩, ⟨v,hv,rfl⟩⟩

/-- A closed regular plane curve cannot have constant vertical height.
Rolle's theorem for the horizontal coordinate supplies an interior label. -/
theorem bottom_lt_top_of_regular {t : ℝ} (hγ : ContDiff ℝ ∞ (c.position t))
    (hp : Function.Periodic (c.position t) c.period) (himm : ∀ u, deriv (c.position t) u ≠ 0) :
    c.bottom t < c.top t := by
  let γ := c.position t
  have hc := c.height_range_of_slice_continuous hγ.continuous
  by_contra! hflat
  have hflat' (u) (hu : u ∈ Icc 0 c.period) : (γ u).im = c.bottom t :=
    le_antisymm ((hc.1 u hu).2.trans hflat) (hc.1 u hu).1
  have hd (u : ℝ) := (hγ.differentiable (by simp) u).hasDerivAt
  have hclose : γ c.period = γ 0 := by simpa using hp 0
  obtain ⟨u,hu,hzero⟩ := exists_hasDerivAt_eq_zero c.period_pos
    (Complex.continuous_re.comp hγ.continuous).continuousOn
    (show (γ 0).re = (γ c.period).re by rw [hclose])
    (f' := fun u => (deriv γ u).re) (fun u _ => Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hd u))
  have he : (fun v => (γ v).im) =ᶠ[𝓝 u] fun _ => c.bottom t := by
    filter_upwards [Icc_mem_nhds hu.1 hu.2] with x hx
    exact hflat' x hx
  have him : (deriv γ u).im=0 := (Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (hd u)).unique
    ((hasDerivAt_const u (c.bottom t)).congr_of_eventuallyEq he)
  exact himm u (Complex.ext hzero him)

/-- If the entire initial image lies above a line and the entire final image
lies below it, the true widths and energies satisfy the cost estimate. -/
theorem whole_halfplane_energy_cost (hflow : c.IsNormalFEF) {T line : ℝ} (hT : 0<T)
    (hslab : Icc 0 T ⊆ I)
    (h0 : ∀ u ∈ Icc 0 c.period, line < (c.position 0 u).im)
    (h1 : ∀ u ∈ Icc 0 c.period, (c.position T u).im < line) :
    widthTransitCost (c.verticalWidth 0) (c.bending 0) +
      widthTransitCost (c.verticalWidth T) (c.bending 0) ≤ T*(c.bending 0-c.bending T) := by
  have ht0 := hslab (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)
  have htT := hslab (show T ∈ Icc 0 T from ⟨hT.le,le_rfl⟩)
  have a := c.height_range_of_slice_continuous (c.position_slice_smooth ht0).continuous
  have b := c.height_range_of_slice_continuous (c.position_slice_smooth htT).continuous
  obtain ⟨u,hu,he⟩ := a.2.1
  obtain ⟨v,hv,hv'⟩ := b.2.2
  have hgap : c.top T<c.bottom 0 := by
    rw [← he,← hv']
    exact (h1 v hv).trans (h0 u hu)
  exact c.separated_halfplanes_energy_cost hflow Complex.imCLM Complex.imCLM_norm.le hgap
    (c.bottom_lt_top_of_regular (c.position_slice_smooth ht0) (c.periodic 0 ht0) (c.immersion 0 ht0))
    (c.bottom_lt_top_of_regular (c.position_slice_smooth htT) (c.periodic T htT) (c.immersion T htT))
    hT hslab a b

end MigrationGeometry.Flow.SmoothPeriodicImmersion
