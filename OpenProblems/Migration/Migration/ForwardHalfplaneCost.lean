import Migration.HalfplaneCost

/-! Initial-inclusive estimate obtained by taking the limit of interior
windows. No backward continuation of the geometric PDE is needed. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

def translatedTime (s : ℝ) : SmoothPeriodicImmersion ((fun x => s+x) ⁻¹' I) where
  time_open := c.time_open.preimage (continuous_const.add continuous_id)
  period := c.period
  period_pos := c.period_pos
  position x u := c.position (s+x) u
  joint_smooth := c.joint_smooth.comp
    (((contDiff_const.add contDiff_fst).prodMk contDiff_snd).contDiffOn)
    (fun _ hz => ⟨hz.1,hz.2⟩)
  periodic _ hx := c.periodic _ hx
  immersion _ hx := c.immersion _ hx

theorem translatedTime_normal (hflow : c.IsNormalFEF) (s : ℝ) : (c.translatedTime s).IsNormalFEF := by
  intro x hx u
  have h := (hflow (s+x) hx u).scomp x ((hasDerivAt_id x).const_add s)
  simpa [translatedTime,Function.comp_def] using h

theorem interior_halfplane_energy_cost (hflow : c.IsNormalFEF) {s t line : ℝ} (hst : s<t)
    (hslab : Icc s t ⊆ I) (hs : ∀ u ∈ Icc 0 c.period, line < (c.position s u).im)
    (ht : ∀ u ∈ Icc 0 c.period, (c.position t u).im < line) :
    widthTransitCost (c.verticalWidth s) (c.bending s) +
      widthTransitCost (c.verticalWidth t) (c.bending s) ≤ (t-s)*(c.bending s-c.bending t) := by
  have hshift : Icc 0 (t-s) ⊆ ((fun x => s+x) ⁻¹' I) := by
    intro x hx
    exact hslab ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have h := (c.translatedTime s).whole_halfplane_energy_cost (c.translatedTime_normal hflow s)
    (line := line) (sub_pos.mpr hst) hshift (by simpa [translatedTime] using hs)
    (by simpa [translatedTime] using ht)
  simpa only [verticalWidth,top,bottom,bending,translatedTime,add_zero,
    show s+(t-s)=t by ring] using h

theorem widthTransitCost_continuous : Continuous (fun z : ℝ × ℝ => widthTransitCost z.1 z.2) := by
  unfold widthTransitCost
  apply (continuous_fst.pow 3).div
    ((continuous_const.add (Real.continuous_sqrt.comp ((continuous_const.mul continuous_snd).mul continuous_fst))).pow 2)
  intro z
  exact pow_ne_zero _ (ne_of_gt (add_pos_of_pos_of_nonneg Real.pi_pos (Real.sqrt_nonneg _)))

variable (d : SmoothPeriodicImmersion (Ioi 0))

/-- Covers a forward trajectory with continuous initial position family and
one-sided continuous bending energy. The PDE is imposed only at positive times. -/
theorem forward_halfplane_energy_cost (hflow : d.IsNormalFEF)
    (hposition : ContinuousOn (fun z : ℝ × ℝ => d.position z.1 z.2) (Ici 0 ×ˢ univ))
    (hbending : ContinuousWithinAt d.bending (Ici 0) 0)
    {T line : ℝ} (hT : 0<T)
    (h0 : ∀ u ∈ Icc 0 d.period, line < (d.position 0 u).im)
    (h1 : ∀ u ∈ Icc 0 d.period, (d.position T u).im < line) :
    widthTransitCost (d.verticalWidth 0) (d.bending 0) +
      widthTransitCost (d.verticalWidth T) (d.bending 0) ≤ T*(d.bending 0-d.bending T) := by
  have hc : Continuous (fun z : ℝ × ℝ => d.position (max z.1 0) z.2) :=
    hposition.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max z.1 0 from le_max_right _ _,mem_univ _⟩)
  have hh : Continuous (fun z : ℝ × ℝ => (d.position (max z.1 0) z.2).im) :=
    Complex.continuous_im.comp hc
  have hlo : Continuous (fun t : ℝ => d.bottom (max t 0)) :=
    isCompact_Icc.continuous_sInf (f := fun t u => (d.position (max t 0) u).im) hh
  have hup : Continuous (fun t : ℝ => d.top (max t 0)) :=
    isCompact_Icc.continuous_sSup (f := fun t u => (d.position (max t 0) u).im) hh
  have hlo' : ContinuousOn d.bottom (Ici 0) := hlo.continuousOn.congr
    (fun t ht => by simp only [max_eq_left (show 0≤t from ht)])
  have hup' : ContinuousOn d.top (Ici 0) := hup.continuousOn.congr
    (fun t ht => by simp only [max_eq_left (show 0≤t from ht)])
  have hz : (0:ℝ) ∈ Ici 0 := by simp
  have hlimB : Tendsto d.bending (𝓝[>] 0) (𝓝 (d.bending 0)) := hbending.mono (show Ioi (0:ℝ) ⊆ Ici 0 from fun _ h => le_of_lt (show (0:ℝ)<_ from h))
  have hlimW : Tendsto d.verticalWidth (𝓝[>] 0) (𝓝 (d.verticalWidth 0)) :=
    ((hup'.sub hlo') 0 hz).mono (show Ioi (0:ℝ) ⊆ Ici 0 from fun _ h => le_of_lt (show (0:ℝ)<_ from h))
  have htime : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hpc : Continuous (d.position 0) := by
    simpa [Function.comp_def] using hc.comp (f := fun u : ℝ => ((0:ℝ),u)) (continuous_const.prodMk continuous_id)
  obtain ⟨u,hu,hm⟩ := (d.height_range_of_slice_continuous hpc).2.1
  have hl0 : line<d.bottom 0 := by rw [← hm]; exact h0 u hu
  have hl : ∀ᶠ s in 𝓝[>] 0, line<d.bottom s :=
    ((hlo' 0 hz).mono (show Ioi (0:ℝ) ⊆ Ici 0 from fun _ h => le_of_lt (show (0:ℝ)<_ from h))).eventually (lt_mem_nhds hl0)
  have hevent : ∀ᶠ s in 𝓝[>] 0,
      widthTransitCost (d.verticalWidth s) (d.bending s) + widthTransitCost (d.verticalWidth T) (d.bending s) ≤
        (T-s)*(d.bending s-d.bending T) := by
    filter_upwards [hl,self_mem_nhdsWithin,htime.eventually (gt_mem_nhds hT)] with s hls hs hst
    have hps := d.height_range_of_slice_continuous (d.position_slice_smooth hs).continuous
    exact d.interior_halfplane_energy_cost hflow hst (fun x hx => lt_of_lt_of_le hs hx.1)
      (fun y hy => hls.trans_le (hps.1 y hy).1) h1
  have hleft := ((widthTransitCost_continuous.tendsto _).comp (hlimW.prodMk_nhds hlimB)).add
    ((widthTransitCost_continuous.tendsto _).comp ((tendsto_const_nhds (x := d.verticalWidth T)).prodMk_nhds hlimB))
  have hright := ((tendsto_const_nhds (x := T)).sub htime).mul
    (hlimB.sub (tendsto_const_nhds (x := d.bending T)))
  simpa only [sub_zero] using (le_of_tendsto_of_tendsto hleft hright hevent)

end MigrationGeometry.Flow.SmoothPeriodicImmersion
