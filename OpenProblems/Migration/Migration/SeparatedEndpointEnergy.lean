import Migration.BendingDissipation
import Migration.StripMass

/-! A numerical lower bound for the time and bending-energy drop required
to move a closed free elastic flow strictly across a line. -/
noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)
open StripCutoff

/-- Minimum and maximum of the actual projected position over one period. -/
def HasHeightRange (H : ℂ →L[ℝ] ℝ) (t lo hi : ℝ) : Prop :=
  (∀ u ∈ Icc 0 c.period, H (c.position t u) ∈ Icc lo hi) ∧
  (∃ u ∈ Icc 0 c.period, H (c.position t u)=lo) ∧
  (∃ v ∈ Icc 0 c.period, H (c.position t v)=hi)

def widthTransitCost (W E : ℝ) : ℝ := W^3/(Real.pi+Real.sqrt (2*E*W))^2

private theorem width_cost_eq {W E : ℝ} (hW : 0 < W) (hE : 0 ≤ E) :
    widthTransitCost W E = (W/(Real.sqrt (2*E)+(Real.pi/W)*Real.sqrt W))^2 := by
  let x := Real.sqrt W
  have hx : 0 < x := Real.sqrt_pos.mpr hW
  have hx2 : x^2=W := Real.sq_sqrt hW.le
  rw [widthTransitCost, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2*E)]
  change W^3/(Real.pi + Real.sqrt (2*E)*x)^2 = (W/(Real.sqrt (2*E)+(Real.pi/W)*x))^2
  rw [← hx2]
  have hden : Real.pi + Real.sqrt (2*E)*x ≠ 0 := ne_of_gt (by positivity)
  have hden' : Real.sqrt (2*E)+(Real.pi/x^2)*x ≠ 0 := ne_of_gt (by positivity)
  field_simp [hx.ne',hden,hden']
  ring

private theorem two_slices_cost (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    {a b W V T B : ℝ} (hgap : b<a) (hW : 0<W) (hV : 0<V) (hT : 0<T) (hB : 0<B)
    (hslab : Icc 0 T ⊆ I) (henergy : ∀ t ∈ Icc 0 T, 2*c.bending t ≤ B^2)
    (h0 : c.HasHeightRange H 0 a (a+W)) (h1 : c.HasHeightRange H T (b-V) b) :
    (W/(B+(Real.pi/W)*Real.sqrt W))^2+(V/(B+(Real.pi/V)*Real.sqrt V))^2 ≤
      T*(c.bending 0-c.bending T) := by
  let k := Real.pi/W
  let l := Real.pi/V
  have hk : 0<k := div_pos Real.pi_pos hW
  have hl : 0<l := div_pos Real.pi_pos hV
  let r := partition a b
  have hr : Continuous r := partition_continuous a b
  have hs : Continuous (fun z => 1-r z) := continuous_const.sub hr
  have hc1 : ∀ z, 0<k*(z-a) → r z=1 := by
    intro z hz
    apply partition_of_high hgap
    by_contra! hn
    exact (not_le_of_gt hz) (mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hn.le))
  have hc2 : ∀ z, 0<(-l)*(z-b) → 1-r z=1 := by
    intro z hz
    have hb : z ≤ b := by
      by_contra! hn
      linarith [mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl.le) (sub_nonneg.mpr hn.le)]
    rw [show r z=0 from partition_of_low hgap hb,sub_zero]
  let upper := scaled k a r hr hc1
  let lower := scaled (-l) b (fun z => 1-r z) hs hc2
  have hsep (z) : upper.localization z ^2+lower.localization z ^2 ≤ 1 := by
    change (r z)^2+(1-r z)^2 ≤ 1
    have hh := partition_mem a b z
    have hz : 0 ≤ r z := hh.1
    have hz' : r z ≤ 1 := hh.2
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hz')]
  obtain ⟨hb0, ⟨u,hu,heu⟩, ⟨v,hv,hev⟩⟩ := h0
  obtain ⟨hb1, ⟨w,hw,hew⟩, ⟨x,hx,hex⟩⟩ := h1
  have hz0 : (0:ℝ) ∈ I := hslab ⟨le_rfl,hT.le⟩
  have hzT : T ∈ I := hslab ⟨hT.le,le_rfl⟩
  have hbase0 := c.scaled_mass_lower H hH hz0 hk.ne' hr hc1 hu hv heu
    (show k*(H (c.position 0 v)-a)=Real.pi by rw [hev]; dsimp [k]; field_simp; ring)
  have hbaseT := c.scaled_mass_lower H hH hzT (neg_ne_zero.mpr hl.ne') hs hc2 hx hw hex
    (show (-l)*(H (c.position T w)-b)=Real.pi by rw [hew]; dsimp [l]; field_simp; ring)
  have hpiW : Real.pi/|k|=W := by rw [abs_of_pos hk]; dsimp [k]; field_simp
  have hpiV : Real.pi/|-l|=V := by rw [abs_neg,abs_of_pos hl]; dsimp [l]; field_simp
  rw [hpiW] at hbase0
  rw [hpiV] at hbaseT
  have hzeroT := c.scaled_mass_zero (t := T) H hr hc1 (fun y hy =>
    mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr ((hb1 y hy).2.trans hgap.le)))
  have hzero0 := c.scaled_mass_zero (t := 0) H hs hc2 (fun y hy =>
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl.le) (sub_nonneg.mpr (hgap.le.trans (hb0 y hy).1)))
  have h := c.two_endpoint_transit_cost hflow H hH upper lower hsep hB hW.le hV.le hT hslab
    henergy hbase0 hzeroT hzero0 hbaseT
  rw [c.full_dissipation_eq_bending_drop hflow H hT.le hslab] at h
  simpa only [upper,lower,scaled,abs_neg,abs_of_pos hk,abs_of_pos hl,k,l] using h

/-- A strict gap between actual endpoint images costs elapsed time times the
actual bending-energy loss. The widths are the attained endpoint ranges.
No cap on curvature derivatives or advance bound on the energy is required. -/
theorem separated_halfplanes_energy_cost (hflow : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ) (hH : ‖H‖ ≤ 1)
    {m₀ M₀ m₁ M₁ T : ℝ} (hgap : M₁<m₀) (hW₀ : m₀<M₀) (hW₁ : m₁<M₁)
    (hT : 0<T) (hslab : Icc 0 T ⊆ I)
    (h0 : c.HasHeightRange H 0 m₀ M₀) (h1 : c.HasHeightRange H T m₁ M₁) :
    widthTransitCost (M₀-m₀) (c.bending 0) + widthTransitCost (M₁-m₁) (c.bending 0) ≤
      T*(c.bending 0-c.bending T) := by
  let W := M₀-m₀
  let V := M₁-m₁
  have hW : 0<W := sub_pos.mpr hW₀
  have hV : 0<V := sub_pos.mpr hW₁
  have h0' : c.HasHeightRange H 0 m₀ (m₀+W) := by simpa [W] using h0
  have h1' : c.HasHeightRange H T (M₁-V) M₁ := by simpa [V] using h1
  have hem : ∀ t ∈ Icc 0 T, c.bending t ≤ c.bending 0 := fun t ht =>
    c.bending_le_of_slab hflow H ht.1 (fun y hy => hslab ⟨hy.1,hy.2.trans ht.2⟩)
  have he : 0<c.bending 0 := by
    by_contra! hn
    have h := c.two_slices_cost hflow H hH hgap hW hV hT (B := 1) (by norm_num)
      hslab (fun t ht => by linarith [hem t ht]) h0' h1'
    have hpos : 0<(W/(1+(Real.pi/W)*Real.sqrt W))^2 := by positivity
    have hnon := sq_nonneg (V/(1+(Real.pi/V)*Real.sqrt V))
    have hrhs : T*(c.bending 0-c.bending T) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hT.le (sub_nonpos.mpr (hn.trans (c.bending_nonneg T)))
    linarith
  have hp : 0 < Real.sqrt (2*c.bending 0) := by positivity
  have hs : (Real.sqrt (2*c.bending 0))^2 = 2*c.bending 0 := Real.sq_sqrt (by positivity)
  rw [width_cost_eq hW he.le, width_cost_eq hV he.le]
  exact c.two_slices_cost hflow H hH hgap hW hV hT hp hslab
    (fun t ht => by rw [hs]; linarith [hem t ht]) h0' h1'

end MigrationGeometry.Flow.SmoothPeriodicImmersion
