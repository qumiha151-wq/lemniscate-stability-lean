import Migration.MultiDiskFluxForward

noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

/-- Two-time support including the full later-radius contribution when the
earlier time is the one-sided initial time. -/
theorem multi_forward_earlier_disk_of_slabs (hf : c.IsNormalFEF) {m : ℝ} (hm : 2≤m)
    (position : ContinuousOn (fun q : ℝ×ℝ=>c.position q.1 q.2) (Ici 0×ˢuniv))
    (energy : ContinuousWithinAt c.bending (Ici 0) 0)
    (center : ContinuousWithinAt c.arclengthCentroid (Ici 0) 0) (ep : 0<c.bending 0)
    (turn : ∀v,0<v → |c.signedCurvatureIntegral v|=2*Real.pi*m)
    (cap : ∀v,0<v → 2*c.bending v*c.coreLength v≤(2*Real.pi*m)^2+Real.pi^2/4)
    {s t : ℝ} (hs : 0≤s) (st : s≤t) :
    Metric.closedBall (c.arclengthCentroid s)
      ((1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending s+(1/200)*(Real.pi*m)/c.bending t)) ⊆
        convexHull ℝ (c.position t '' Icc 0 c.period) := by
  rcases eq_or_lt_of_le hs with rfl|ps
  · rcases eq_or_lt_of_le st with rfl|pt
    · rw [show (1+(1/m)^2/16)*((54/100)*(Real.pi*m)/c.bending 0+(1/200)*(Real.pi*m)/c.bending 0)=
          (1+(1/m)^2/16)*(109/200)*(Real.pi*m)/c.bending 0 by ring]
      exact c.multi_forward_disk_of_slabs hf hm position energy center ep turn cap le_rfl
    let C:=1+(1/m)^2/16
    let A:=(54/100)*(Real.pi*m)
    let B:=(1/200)*(Real.pi*m)/c.bending t
    let R:=fun v=>C*(A/c.bending v+B)
    have mp : 0<m := by linarith
    have et:=c.bending_pos_of_width pt
    have cp : 0<C := by dsimp [C];positivity
    have ap : 0<A := by dsimp [A];positivity
    have bp : 0<B := by dsimp [B];positivity
    have rp : 0<R 0 := mul_pos cp (add_pos (div_pos ap ep) bp)
    have inc : Ioi (0:ℝ)⊆Ici 0 := Ioi_subset_Ici_self
    have rlim : Tendsto R (𝓝[>] 0) (𝓝 (R 0)) :=
      tendsto_const_nhds.mul (((tendsto_const_nhds (x:=A)).div (energy.mono inc).tendsto ep.ne').add_const B)
    let K:=convexHull ℝ (c.position t '' Icc 0 c.period)
    have closed : IsClosed K := (MigrationGeometry.SimilarityHull.compact_convexHull
      (isCompact_Icc.image (c.position_slice_smooth pt).continuous)).isClosed
    intro z hz
    let zz:=fun v=>c.arclengthCentroid v+(R v/R 0) • (z-c.arclengthCentroid 0)
    have zzlim : Tendsto zz (𝓝[>] 0) (𝓝 z) := by
      have h:=(center.mono inc).tendsto.add ((rlim.div_const (R 0)).smul (tendsto_const_nhds (x:=z-c.arclengthCentroid 0)))
      simpa [zz,div_self rp.ne'] using h
    apply closed.mem_of_tendsto zzlim
    have before : ∀ᶠ v in 𝓝[>] (0:ℝ), v<t := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds pt)
    filter_upwards [self_mem_nhdsWithin,before] with v (hv : 0<v) vt
    have sub : Icc v t⊆Ioi 0:=fun r hr=>lt_of_lt_of_le hv hr.1
    have rv : 0<R v:=mul_pos cp (add_pos (div_pos ap (c.bending_pos_of_width hv)) bp)
    apply c.multi_disk_on_abs_bending_slab hf hm vt.le sub (fun r hr=>turn r (sub hr)) (fun r hr=>cap r (sub hr))
    rw [Metric.mem_closedBall,dist_eq_norm] at hz ⊢
    change ‖z-c.arclengthCentroid 0‖≤R 0 at hz
    change ‖zz v-c.arclengthCentroid v‖≤R v
    dsimp only [zz]
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos rv rp)]
    exact (mul_le_mul_of_nonneg_left hz (div_pos rv rp).le).trans_eq (div_mul_cancel₀ _ rp.ne')
  · have sub : Icc s t⊆Ioi 0:=fun r hr=>lt_of_lt_of_le ps hr.1
    exact c.multi_disk_on_abs_bending_slab hf hm st sub (fun r hr=>turn r (sub hr)) (fun r hr=>cap r (sub hr))

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_forward_earlier_disk_of_slabs

