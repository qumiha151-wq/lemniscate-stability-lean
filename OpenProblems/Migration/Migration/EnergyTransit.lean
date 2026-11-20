import Migration.StripCurvature

/-! A complete migration costs a fixed positive amount on the energy
scale. No a priori bound on the width or on curvature derivatives occurs. -/
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion

private theorem scaled_width_cost {E W : ℝ} (hm : 2≤E*W) :
    8/(Real.pi+2)^2 ≤ E^3*widthTransitCost W E := by
  let x := E*W
  let y := Real.sqrt (2*E*W)
  have hx : 2≤x := hm
  have hx0 : 0≤x := by linarith
  have hy : 0≤y := Real.sqrt_nonneg _
  have hy2 : y^2=2*x := by
    dsimp [y,x]
    rw [Real.sq_sqrt (by linarith : 0≤2*E*W)]
    ring
  have hyx : y≤x := by nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx)]
  have hp := Real.pi_pos
  have hratio : 2/(Real.pi+2) ≤ x/(Real.pi+y) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hx)]
  have hpow := pow_le_pow_left₀ (by positivity : 0≤2/(Real.pi+2)) hratio 2
  calc
    8/(Real.pi+2)^2 = 2*(2/(Real.pi+2))^2 := by rw [div_pow]; ring
    _ ≤ x*(x/(Real.pi+y))^2 := mul_le_mul hx hpow (sq_nonneg _) hx0
    _ = E^3*widthTransitCost W E := by dsimp [x,y,widthTransitCost]; rw [div_pow]; ring

private theorem combine_scaled_cost {E F W V T : ℝ} (hE : 0≤E) (hF : 0≤F)
    (hW : 2≤E*W) (hV : 2≤F*V) (hT : 0<T)
    (hcost : widthTransitCost W E+widthTransitCost V E≤T*(E-F)) :
    16/(Real.pi+2)^2 ≤ T*E^3*(E-F) := by
  have hW0 : 0≤W := by
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos hE hn.le]
  have hV0 : 0≤V := by
    by_contra! hn
    linarith [mul_nonpos_of_nonneg_of_nonpos hF hn.le]
  have hpos : 0≤widthTransitCost W E+widthTransitCost V E := by unfold widthTransitCost; positivity
  have hFE : F≤E := by
    by_contra! hn
    exact (not_lt_of_ge (hpos.trans hcost)) (mul_neg_of_pos_of_neg hT (sub_neg.mpr hn))
  have hEV := hV.trans (mul_le_mul_of_nonneg_right hFE hV0)
  have h := add_le_add (scaled_width_cost hW) (scaled_width_cost hEV)
  have h' := mul_le_mul_of_nonneg_left hcost (pow_nonneg hE 3)
  calc
    _ = 8/(Real.pi+2)^2+8/(Real.pi+2)^2 := by ring
    _ ≤ _ := h
    _ = E^3*(widthTransitCost W E+widthTransitCost V E) := by ring
    _ ≤ _ := h'
    _ = _ := by ring

variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

theorem whole_halfplane_energy_scale (hflow : c.IsNormalFEF) {T line : ℝ} (hT : 0<T)
    (hslab : Icc 0 T ⊆ I)
    (h0 : ∀ u ∈ Icc 0 c.period, line < (c.position 0 u).im)
    (h1 : ∀ u ∈ Icc 0 c.period, (c.position T u).im < line) :
    16/(Real.pi+2)^2 ≤ T*(c.bending 0)^3*(c.bending 0-c.bending T) := by
  apply combine_scaled_cost (c.bending_nonneg 0) (c.bending_nonneg T)
    (c.bending_mul_verticalWidth (hslab ⟨le_rfl,hT.le⟩))
    (c.bending_mul_verticalWidth (hslab ⟨hT.le,le_rfl⟩)) hT
  exact c.whole_halfplane_energy_cost hflow hT hslab h0 h1

variable (d : SmoothPeriodicImmersion (Ioi 0))

theorem forward_initial_bending_mul_verticalWidth
    (hposition : ContinuousOn (fun z : ℝ × ℝ => d.position z.1 z.2) (Ici 0 ×ˢ univ))
    (hbending : ContinuousWithinAt d.bending (Ici 0) 0) :
    2 ≤ d.bending 0*d.verticalWidth 0 := by
  have hc : Continuous (fun z : ℝ × ℝ => d.position (max z.1 0) z.2) :=
    hposition.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun z => ⟨show 0 ≤ max z.1 0 from le_max_right _ _,mem_univ _⟩)
  have hh : Continuous (fun z : ℝ × ℝ => (d.position (max z.1 0) z.2).im) := Complex.continuous_im.comp hc
  have hlo : Continuous (fun t : ℝ => d.bottom (max t 0)) :=
    isCompact_Icc.continuous_sInf (f := fun t u => (d.position (max t 0) u).im) hh
  have hup : Continuous (fun t : ℝ => d.top (max t 0)) :=
    isCompact_Icc.continuous_sSup (f := fun t u => (d.position (max t 0) u).im) hh
  have hw : ContinuousOn d.verticalWidth (Ici 0) := (hup.sub hlo).continuousOn.congr
    (fun t ht => by simp only [Pi.sub_apply,verticalWidth,max_eq_left (show 0≤t from ht)])
  have sub : Ioi (0:ℝ) ⊆ Ici 0 := fun _ h => le_of_lt (show (0:ℝ)<_ from h)
  have hlim := (hbending.mono sub).tendsto.mul (((hw 0 (by simp)).mono sub).tendsto)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact d.bending_mul_verticalWidth ht

/-- Initial data can be included using only forward regularity and the
two right continuity conditions. -/
theorem forward_halfplane_energy_scale (hflow : d.IsNormalFEF)
    (hposition : ContinuousOn (fun z : ℝ × ℝ => d.position z.1 z.2) (Ici 0 ×ˢ univ))
    (hbending : ContinuousWithinAt d.bending (Ici 0) 0)
    {T line : ℝ} (hT : 0<T)
    (h0 : ∀ u ∈ Icc 0 d.period, line < (d.position 0 u).im)
    (h1 : ∀ u ∈ Icc 0 d.period, (d.position T u).im < line) :
    16/(Real.pi+2)^2 ≤ T*(d.bending 0)^3*(d.bending 0-d.bending T) :=
  combine_scaled_cost (d.bending_nonneg 0) (d.bending_nonneg T)
    (d.forward_initial_bending_mul_verticalWidth hposition hbending)
    (d.bending_mul_verticalWidth hT) hT (d.forward_halfplane_energy_cost hflow hposition hbending hT h0 h1)

end MigrationGeometry.Flow.SmoothPeriodicImmersion
