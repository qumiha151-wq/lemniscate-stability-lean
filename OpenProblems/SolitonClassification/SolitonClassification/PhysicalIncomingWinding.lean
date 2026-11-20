import SolitonClassification.PhysicalIncomingCrossing

noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam
open Set MeasureTheory OuterStress

private theorem spin_nonnegative {δ t ρ : ℝ} {r U w a b : ℝ → ℝ}
    (d : Rates δ t r U w a b) (rho : 0≤ρ) (rad : a t^2+b t^2=ρ^2)
    (deep : ρ*δ≤r t^3) : 0≤Angle.spin δ r U w a b t := by
  let u := U t^2/2
  let p := w t*a t+u*b t
  have osc : w t^2+u^2=1 := by dsimp [u]; linarith only [d.oscillator]
  have ad : |U t| ≤ 2 := by
    have e : U t^2/2 ≤ 1 := by nlinarith only [d.oscillator,sq_nonneg (w t),sq_nonneg (U t^2/2-1)]
    apply abs_le.mpr
    exact ⟨by nlinarith [sq_nonneg (U t+1)],by nlinarith [sq_nonneg (U t-1)]⟩
  have iden : p^2+(w t*b t-u*a t)^2 = (w t^2+u^2)*(a t^2+b t^2) := by unfold p; ring
  rw [osc,rad,one_mul] at iden
  have pd : |p|≤ρ := le_of_sq_le_sq (by rw [sq_abs]; nlinarith [sq_nonneg (w t*b t-u*a t)]) rho
  have pr := mul_le_mul ad pd (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  rw [←abs_mul] at pr
  have v := (neg_abs_le (U t*p)).trans' (neg_le_neg pr)
  have dp := d.delta_pos
  have rp := d.pos
  have num : 0≤2*r t^3+δ*(U t*p) := by
    nlinarith only [deep,mul_le_mul_of_nonneg_left v dp.le]
  unfold Angle.spin Angle.fast
  apply mul_nonneg (by positivity)
  change 0≤r t/δ+U t*p/(2*r t^2)
  apply (le_of_mul_le_mul_right (a := δ*(2*r t^2)) _ (by positivity))
  field_simp [dp.ne',rp.ne']; linarith

theorem positive_amplitude_on_physical_strip {b T : ℝ} (hb : 32≤b)
    (strip : ∀s∈Icc (1:ℝ) T, regular (centreAt b s) ∧ 1 ≤ innerRoot (centreAt b s)) :
    ∀ s ∈ Icc (0:ℝ) T, 0<(centreData b (by linarith)).amplitude s := by
  have bp : 0<b := by linarith
  let z := centreData b bp
  let δ := b⁻¹
  let x := centreAt b
  have dp : 0<δ := inv_pos.mpr bp
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by simp [z,centreData,ofSupport,solution_zero,bp.ne']
  have dz := solution_derivative 1 (![0,b,0,0] : Phase)
  intro s hs
  rcases le_total s 1 with h|h
  · have sq := pow_le_pow_left₀ hs.1 h 2
    linarith [(z.centre_bounds dp init.1 init.2.1 init.2.2.1 init.2.2.2 hs.1).2]
  · have reg := (strip s ⟨h,hs.2⟩).1
    have eq := (outer_chart dp _ dz s reg).1
    change z.root s=Real.sqrt δ*root (x s) at eq
    apply Real.sqrt_pos.mp
    change 0<z.root s
    rw [eq]
    exact mul_pos (Real.sqrt_pos.mpr dp) (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr reg.2))

/-- The true initial lift still winds at the macroscopic incoming section.
    This holds for every terminal time on a regular strip of inner radius at
    least one, without continuity of its selection in the shooting marker. -/
theorem winding_on_physical_strip {b T : ℝ} (hb : 32≤b) (one : 1≤T)
    (strip : ∀s∈Icc (1:ℝ) T, regular (centreAt b s) ∧ 1 ≤ innerRoot (centreAt b s)) :
    let z := centreData b (by linarith)
    let θ := fun t => ∫ v in (0:ℝ)..t, Angle.spin b⁻¹ z.root z.shape z.slope z.along z.across v
    b/8≤θ T ∧ Angle.sn z.shape T=Real.sin (θ T) ∧ Angle.cs z.shape z.slope T=Real.cos (θ T) := by
  dsimp only
  have bp : 0<b := by linarith
  let z := centreData b bp
  let δ := b⁻¹
  let x := centreAt b
  let g := Angle.spin δ z.root z.shape z.slope z.along z.across
  have dp : 0<δ := inv_pos.mpr bp
  have Tpos : 0≤T := by linarith
  have init : z.K 0=0 ∧ z.V 0=1 ∧ z.p 0=0 ∧ z.q 0=0 := by
    simp [z,centreData,ofSupport,solution_zero,bp.ne']
  have dz := solution_derivative 1 (![0,b,0,0] : Phase)
  have pos := positive_amplitude_on_physical_strip hb strip
  have data (s : ℝ) (hs : s∈Icc (0:ℝ) T) := z.normalized_rates s (pos s hs) dp
  have intg : IntervalIntegrable g volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le Tpos]
    exact fun s hs => (Angle.spin_continuousAt (data s hs)).continuousWithinAt
  have tail : 0≤∫ s in (1:ℝ)..T, g s := by
    apply intervalIntegral.integral_nonneg one
    intro s hs
    have reg := (strip s hs).1
    have far := (strip s hs).2
    have cube := (outer_chart dp _ dz s reg).2.2.2.2.2.1
    change innerRoot (x s)^3*outerRadius δ (x s)*δ = z.root s^3 at cube
    have rp : 0≤outerRadius δ (x s) := mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.rpow_pos_of_pos reg.1 _).le _)
    have full : s∈Icc (0:ℝ) T := ⟨by linarith [hs.1],hs.2⟩
    have rad := radius_identity dp _ dz s
    change (outerRadius δ (x s))^2=z.p s^2+z.q s^2 at rad
    apply spin_nonnegative (data s full) rp ((z.radius_sq s (pos s full)).trans rad.symm)
    have pw := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) far 3
    rw [one_pow] at pw
    rw [←cube]
    exact mul_le_mul_of_nonneg_right ((by simpa only [one_mul] using mul_le_mul_of_nonneg_right pw rp)) dp.le
  have add := intervalIntegral.integral_add_adjacent_intervals
    (intg.mono_set (show uIcc 0 1 ⊆ uIcc 0 T by simpa [uIcc_of_le Tpos,uIcc_of_le zero_le_one] using Icc_subset_Icc_right one))
    (intg.mono_set (show uIcc 1 T ⊆ uIcc 0 T by simpa [uIcc_of_le Tpos,uIcc_of_le one] using Icc_subset_Icc_left zero_le_one))
  have start : b/8≤∫ t in (0:ℝ)..1, g t := (physical_centre_winding hb).2
  have az : z.amplitude 0=1 := by norm_num [OuterStress.Data.amplitude,init.1,init.2.1]
  have lift := Angle.physical_phase_lift Tpos data (by simp [Angle.sn,OuterStress.Data.shape,init.1])
    (by simp [Angle.cs,OuterStress.Data.shape,OuterStress.Data.slope,init.1,init.2.1,az]) T (right_mem_Icc.mpr Tpos)
  exact ⟨by change b/8 ≤ ∫ t in (0:ℝ)..T, g t; linarith,lift⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.winding_on_physical_strip
