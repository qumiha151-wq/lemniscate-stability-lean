import Migration.StripCurvature

noncomputable section
open Set MeasureTheory
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)
open StripCutoff

private theorem height_intermediate (H : ℂ →L[ℝ] ℝ) {t lo hi h : ℝ} (ht : t∈I)
    (hz : c.HasHeightRange H t lo hi) (hh : h∈Icc lo hi) :
    ∃ u ∈ Icc 0 c.period, H (c.position t u) = h := by
  obtain ⟨_,⟨u,hu,he⟩,⟨v,hv,hv'⟩⟩ := hz
  have hc := H.continuous.comp (c.position_slice_smooth ht).continuous
  rcases le_total u v with huv | hvu
  · obtain ⟨x,hx,eq⟩ := intermediate_value_Icc huv hc.continuousOn
      (show h∈Icc (H (c.position t u)) (H (c.position t v)) by rwa [he,hv'])
    exact ⟨x,⟨hu.1.trans hx.1,hx.2.trans hv.2⟩,eq⟩
  · obtain ⟨x,hx,eq⟩ := intermediate_value_Icc' hvu hc.continuousOn
      (show h∈Icc (H (c.position t u)) (H (c.position t v)) by rwa [he,hv'])
    exact ⟨x,⟨hv.1.trans hx.1,hx.2.trans hu.2⟩,eq⟩

private theorem recession_from_zero (hf : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    (hH : ‖H‖ ≤ 1) {T d lo hi : ℝ} (hT : 0 < T) (hd : 0 < d)
    (hW : d ≤ hi-lo) (hslab : Icc 0 T ⊆ I) (hE : 0 < c.bending 0)
    (hr : c.HasHeightRange H 0 lo hi) (hlater : ∀ u ∈ Icc 0 c.period, H (c.position T u) ≤ hi-d) :
    (d/(Real.sqrt (2*c.bending 0)+(Real.pi/d)*Real.sqrt d))^2 ≤
      T*(c.bending 0-c.bending T) := by
  let k := Real.pi/d
  let a := hi-d
  let loc := fun _ : ℝ => (1:ℝ)
  have hc : Continuous loc := continuous_const
  have cover (z : ℝ) (_ : 0 < k*(z-a)) : loc z=1 := rfl
  let χ := scaled k a loc hc cover
  have hk : 0<k := div_pos Real.pi_pos hd
  have ht₀ : 0∈I := hslab ⟨le_rfl,hT.le⟩
  obtain ⟨u,hu,hbase⟩ := c.height_intermediate H ht₀ hr
    (show a ∈ Icc lo hi from ⟨by dsimp [a]; linarith,by dsimp [a]; linarith⟩)
  obtain ⟨v,hv,hpeak⟩ := hr.2.2
  have hpi : k*(H (c.position 0 v)-a) = Real.pi := by rw [hpeak]; dsimp [k,a]; field_simp; ring
  have hstart := c.scaled_mass_lower H hH ht₀ hk.ne' hc cover hu hv hbase hpi
  have hpk : Real.pi/|k|=d := by rw [abs_of_pos hk]; dsimp [k]; field_simp
  rw [hpk] at hstart
  have hend := c.scaled_mass_zero H hc cover (fun u hu =>
    mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr (hlater u hu)))
  have hB : 0 < Real.sqrt (2*c.bending 0) := Real.sqrt_pos.mpr (by positivity)
  have hbound (t) (ht : t ∈ Icc 0 T) : 2*c.bending t ≤ (Real.sqrt (2*c.bending 0))^2 := by
    rw [Real.sq_sqrt (by positivity)]
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    linarith [c.bending_le_of_slab hf H ht.1 (hsub.trans hslab)]
  have cost := c.actual_cutoff_transit_cost hf H hH χ.deriv_weight χ.derivative_continuous
    χ.localization_continuous χ.slope_nonneg hB hd.le hT χ.weight_nonneg χ.weight_le_one
    χ.gradient_bound χ.localization_one hslab hbound (Or.inl ⟨hstart,hend⟩)
  change (d/(Real.sqrt (2*c.bending 0)+|k| * Real.sqrt d))^2 ≤
    T*(∫ t in 0..T, c.localDissipation H (fun _ => 1) t) at cost
  rw [abs_of_pos hk,c.full_dissipation_eq_bending_drop hf H hT.le hslab] at cost
  exact cost

/-- Recession of a single directional support by a physical distance
`d` incurs an explicit physical time times energy-drop cost. -/
theorem support_recession_cost (hf : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    (hH : ‖H‖ ≤ 1) {s t d lo hi : ℝ} (hst : s < t) (hd : 0 < d)
    (hW : d ≤ hi-lo) (hslab : Icc s t ⊆ I) (hE : 0<c.bending s)
    (hr : c.HasHeightRange H s lo hi) (hlater : ∀ u ∈ Icc 0 c.period, H (c.position t u) ≤ hi-d) :
    (d/(Real.sqrt (2*c.bending s)+(Real.pi/d)*Real.sqrt d))^2 ≤
      (t-s)*(c.bending s-c.bending t) := by
  have hshift : Icc 0 (t-s) ⊆ ((fun x => s+x) ⁻¹' I) := by
    intro v hv
    exact hslab ⟨by linarith [hv.1],by linarith [hv.2]⟩
  have h := (c.translatedTime s).recession_from_zero (c.translatedTime_normal hf s) H hH
    (sub_pos.mpr hst) hd hW hshift (by simpa [translatedTime,bending] using hE)
    (by simpa [translatedTime,HasHeightRange] using hr)
    (by simpa [translatedTime] using hlater)
  simpa [translatedTime,bending] using h

/-- Dimensionless cost for a recession whose distance is `η/E(s)`. -/
theorem scaled_support_recession_cost (hf : c.IsNormalFEF) (H : ℂ →L[ℝ] ℝ)
    (hH : ‖H‖ ≤ 1) {s t η lo hi : ℝ} (hst : s < t) (hη : 0 < η)
    (hW : η/c.bending s ≤ hi-lo) (hslab : Icc s t ⊆ I) (hE : 0<c.bending s)
    (hr : c.HasHeightRange H s lo hi)
    (hlater : ∀ u ∈ Icc 0 c.period, H (c.position t u) ≤ hi-η/c.bending s) :
    η^3/(Real.pi+Real.sqrt (2*η))^2 ≤ (t-s)*c.bending s^3*(c.bending s-c.bending t) := by
  let E := c.bending s
  let d := η/E
  have hd : 0<d := div_pos hη hE
  have h := c.support_recession_cost hf H hH hst hd hW hslab hE hr hlater
  have eq : (d/(Real.sqrt (2*E)+(Real.pi/d)*Real.sqrt d))^2*E^3 =
      η^3/(Real.pi+Real.sqrt (2*η))^2 := by
    have hEd : E*d=η := by dsimp [d]; field_simp [show E≠0 from hE.ne']
    let x := Real.sqrt d
    have hy : x^2 = d := Real.sq_sqrt hd.le
    have hz : Real.sqrt (2*η)=Real.sqrt (2*E)*x := by
      dsimp [x]
      rw [← Real.sqrt_mul (show 0≤2*E by dsimp [E]; positivity),mul_assoc,hEd]
    have hx : 0 < x := Real.sqrt_pos.mpr hd
    have hs : 0 < Real.sqrt (2*E) := Real.sqrt_pos.mpr (by dsimp [E]; positivity)
    change (d/(Real.sqrt (2*E)+(Real.pi/d)*x))^2*E^3 = _
    rw [hz,← hEd,← hy]
    have hden : Real.pi + Real.sqrt (2*E)*x ≠ 0 := by positivity
    have hden' : Real.sqrt (2*E)+(Real.pi/x^2)*x ≠ 0 := by positivity
    field_simp [hden,hden',hx.ne']
    ring
  rw [← eq]
  have hh := mul_le_mul_of_nonneg_right h (pow_nonneg hE.le 3)
  dsimp only [E] at *
  linarith

#print axioms support_recession_cost
#print axioms scaled_support_recession_cost
end MigrationGeometry.Flow.SmoothPeriodicImmersion
