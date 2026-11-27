import Migration.IntrinsicBendingPast
import Migration.LowDefectMaterialModes

noncomputable section
open Set MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

/-- The square of the true normal material displacement is controlled by the
time integral of any continuous envelope of the actual elastic force. -/
theorem material_displacement_sq_le_force (hf : c.IsNormalFEF)
    {s t : ℝ} (st : s ≤ t) (slab : Icc s t ⊆ I) (u : ℝ)
    (A : ℝ → ℝ) (hA : Continuous A)
    (forceBound : ∀v ∈ Icc s t, |force (c.position v) u| ≤ A v) :
    ‖c.position t u-c.position s u‖^2 ≤ (t-s)*(∫v in s..t,A v^2) := by
  have cv : ContinuousOn (fun v => c.velocity v u) (Icc s t) :=
    c.velocity_joint_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun v hv => ⟨slab hv,mem_univ u⟩)
  have int := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le st
    (f:=fun v=>c.position v u) (f':=fun v=>c.velocity v u)
    (fun v hv => (c.position_time_hasDerivAt (slab hv) u).continuousAt.continuousWithinAt)
    (fun v hv => c.position_time_hasDerivAt (slab ⟨hv.1.le,hv.2.le⟩) u)
    (cv.intervalIntegrable_of_Icc st)
  have m := intervalIntegral.integral_mono_on (μ:=volume) st (cv.norm.intervalIntegrable_of_Icc st)
    (hA.intervalIntegrable ..) (fun v hv => by
      change ‖c.velocity v u‖≤A v
      simpa only [c.velocity_eq_normal hf (slab hv) u,norm_smul,Real.norm_eq_abs,abs_neg,
        normal_unit (c.immersion v (slab hv)),mul_one] using forceBound v hv)
  have tri := intervalIntegral.norm_integral_le_integral_norm (μ:=volume) (f:=fun v=>c.velocity v u) st
  rw [int] at tri
  have cs := interval_integral_mul_sq_le (f:=fun _:ℝ=>1) (g:=A) continuous_const hA st
  simp only [one_mul,one_pow,intervalIntegral.integral_const,smul_eq_mul,mul_one] at cs
  exact (pow_le_pow_left₀ (norm_nonneg _) (tri.trans m) 2).trans cs

/-- A strict half-plane crossing requires this amount of squared maximum
speed on the time interval, even when the energy or turning is arbitrarily high. -/
theorem separated_force_cost_at_start (hf : c.IsNormalFEF) {s t r : ℝ}
    (st : s ≤ t) (slab : Icc s t ⊆ I) (rp : 0 < r)
    (hb : (c.materialSlice (slab ⟨le_rfl,st⟩)).localBendingBound r)
    (e : ℂ) (he : ‖e‖=1) (level : ℝ)
    (initial : ∀u∈Icc 0 c.period,inner ℝ e (c.position s u) ≤ level)
    (terminal : ∀u∈Icc 0 c.period,level < inner ℝ e (c.position t u))
    (A : ℝ → ℝ) (hA : Continuous A)
    (hforce : ∀v∈Icc s t,∀u∈Icc 0 c.period, |force (c.position v) u|≤A v) :
    (r/2)^2 < (t-s)*(∫v in s..t,A v^2) := by
  let p := c.materialSlice (slab ⟨le_rfl,st⟩)
  obtain ⟨_,⟨j,hj,rfl⟩,_,⟨u,hu,rfl⟩,height⟩ := p.width_of_local_bending rp hb e he
  change r/2 ≤ inner ℝ e (c.position s j)-inner ℝ e (c.position s u) at height
  have unit := real_inner_le_norm e (c.position t u-c.position s u)
  rw [inner_sub_right,he,one_mul] at unit
  have moved : r/2<‖c.position t u-c.position s u‖ := by
    linarith only [height,initial j hj,terminal u hu,unit]
  exact (sq_lt_sq' (by linarith only [rp,norm_nonneg (c.position t u-c.position s u)]) moved).trans_le
    (c.material_displacement_sq_le_force hf st slab u A hA (fun v hv=>hforce v hv u hu))

/-- Using the width of the terminal slice also requires this much squared maximum
speed on the time interval, even when the energy or turning is arbitrarily high. -/
theorem separated_force_cost_at_end (hf : c.IsNormalFEF) {s t r : ℝ}
    (st : s ≤ t) (slab : Icc s t ⊆ I) (rp : 0 < r)
    (hb : (c.materialSlice (slab ⟨st,le_rfl⟩)).localBendingBound r)
    (e : ℂ) (he : ‖e‖=1) (level : ℝ)
    (initial : ∀u∈Icc 0 c.period,inner ℝ e (c.position s u) ≤ level)
    (terminal : ∀u∈Icc 0 c.period,level < inner ℝ e (c.position t u))
    (A : ℝ → ℝ) (hA : Continuous A)
    (hforce : ∀v∈Icc s t,∀u∈Icc 0 c.period, |force (c.position v) u|≤A v) :
    (r/2)^2 < (t-s)*(∫v in s..t,A v^2) := by
  let p := c.materialSlice (slab ⟨st,le_rfl⟩)
  obtain ⟨_,⟨j,hj,rfl⟩,_,⟨u,hu,rfl⟩,height⟩ := p.width_of_local_bending rp hb e he
  change r/2 ≤ inner ℝ e (c.position t j)-inner ℝ e (c.position t u) at height
  have unit := real_inner_le_norm e (c.position t j-c.position s j)
  rw [inner_sub_right,he,one_mul] at unit
  have moved : r/2<‖c.position t j-c.position s j‖ := by
    linarith only [height,initial j hj,terminal u hu,unit]
  exact (sq_lt_sq' (by linarith only [rp,norm_nonneg (c.position t j-c.position s j)]) moved).trans_le
    (c.material_displacement_sq_le_force hf st slab j A hA (fun v hv=>hforce v hv j hj))

end MigrationGeometry.Flow.SmoothPeriodicImmersion

#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.separated_force_cost_at_end
