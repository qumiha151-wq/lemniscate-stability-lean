import Migration.MultiDiskBendingBarrier
import Migration.MultiDiskTurning

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable (c : SmoothPeriodicImmersion (Ioi 0))

private theorem multi_forward_threshold (hf : c.IsNormalFEF) {S C : ℝ} (six : 6≤S)
    (product : ContinuousWithinAt (fun t=>2*c.bending t*c.coreLength t) (Ici 0) 0)
    (turn : ∀v,0<v → |c.signedCurvatureIntegral v|=S)
    (floor : S^2≤C) (room : C<(S+3/5)^2)
    (initial : 2*c.bending 0*c.coreLength 0≤C) {t : ℝ} (ht : 0<t) :
    2*c.bending t*c.coreLength t≤C := by
  let U := fun t=>2*c.bending t*c.coreLength t
  have cu : ContinuousWithinAt U (Ioi 0) 0 := product.mono Ioi_subset_Ici_self
  by_contra! high
  have hhigh : C<U t := high
  let b := min (U t) ((S+3/5)^2)
  let M := (C+b)/2
  have gap : C<b := lt_min hhigh room
  have larger : C<M := by dsimp only [M];linarith
  have smaller : M<b := by dsimp only [M];linarith
  have threshold := cu.eventually_lt_const (lt_of_le_of_lt initial larger)
  have time : ∀ᶠv in 𝓝[>] (0:ℝ), v<t := (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds ht)
  have after : ∀ᶠv in 𝓝[>] (0:ℝ), 0<v := self_mem_nhdsWithin
  obtain ⟨v,hv,vt,hvM⟩ := (after.and (time.and threshold)).exists
  have slab : Icc v t⊆Ioi 0 := fun x hx=>lt_of_lt_of_le hv hx.1
  have bound := c.multi_bending_on_slab hf vt.le slab six (fun x hx=>turn x (slab hx))
    (floor.trans_lt larger) (smaller.le.trans (min_le_right _ _)) hvM.le t ⟨vt.le,le_rfl⟩
  exact (not_lt_of_ge bound) (smaller.trans_le (min_le_left _ _))

/-- Throughout positive time the normalized bending product cannot exceed
its initial value, including data that attain the exact multiply-covered
circle lower bound at the initial time. -/
theorem multi_bending_product_from_zero (hf : c.IsNormalFEF) {m : ℝ} (hm : 2≤m)
    (product : ContinuousWithinAt (fun t=>2*c.bending t*c.coreLength t) (Ici 0) 0)
    (turn : ∀v,0<v → |c.signedCurvatureIntegral v|=2*Real.pi*m)
    (initial : 2*c.bending 0*c.coreLength 0≤(2*Real.pi*m)^2+Real.pi^2/4) :
    ∀v,0<v → 2*c.bending v*c.coreLength v≤2*c.bending 0*c.coreLength 0 := by
  let S := 2*Real.pi*m
  let U := fun t=>2*c.bending t*c.coreLength t
  have six : 6≤S := by
    dsimp only [S];nlinarith only [mul_le_mul_of_nonneg_left hm (show 0≤2*Real.pi by positivity),Real.pi_gt_three]
  have min_energy (v : ℝ) (hv : 0<v) : S^2≤U v := by
    let p := c.materialSlice hv
    have en : p.bendingCurve.energy=c.bending v := p.bendingCurve_energy
    have len : p.bendingCurve.period=c.coreLength v := rfl
    have total : (∫s in 0..p.bendingCurve.period,p.bendingCurve.curvature s)=c.signedCurvatureIntegral v := p.bendingCurve_turn
    have h := p.bendingCurve.multi_bending_slice.1
    rw [total,turn v hv,en,len] at h
    have nn : 0≤U v := by
      change 0≤2*c.bending v*c.coreLength v
      have ev := en ▸ p.bendingCurve.energy_pos
      have lv := c.coreLength_pos hv
      positivity
    have sq := pow_le_pow_left₀ (by linarith : 0≤S) h 2
    change S^2≤(Real.sqrt (U v))^2 at sq
    rwa [Real.sq_sqrt nn] at sq
  have floor : S^2≤U 0 := by
    by_contra! low
    have near : ContinuousWithinAt U (Ioi 0) 0 := product.mono Ioi_subset_Ici_self
    have after : ∀ᶠv in 𝓝[>] (0:ℝ),0<v := self_mem_nhdsWithin
    obtain ⟨v,hv,bad⟩ := (after.and (near.eventually_lt_const low)).exists
    exact (not_lt_of_ge (min_energy v hv)) bad
  have room : U 0<(S+3/5)^2 := by
    change U 0≤S^2+Real.pi^2/4 at initial
    have q := mul_pos (sub_pos.mpr Real.pi_lt_four) (show 0<Real.pi+4 by positivity)
    nlinarith only [initial,six,q]
  exact fun _ hv=>c.multi_forward_threshold hf six product turn floor room le_rfl hv

theorem multi_bending_cap_from_zero (hf : c.IsNormalFEF) {m : ℝ} (hm : 2≤m)
    (product : ContinuousWithinAt (fun t=>2*c.bending t*c.coreLength t) (Ici 0) 0)
    (turn : ∀v,0<v → |c.signedCurvatureIntegral v|=2*Real.pi*m)
    (initial : 2*c.bending 0*c.coreLength 0≤(2*Real.pi*m)^2+Real.pi^2/4) :
    ∀v,0<v → 2*c.bending v*c.coreLength v≤(2*Real.pi*m)^2+Real.pi^2/4 :=
  fun v hv=>(c.multi_bending_product_from_zero hf hm product turn initial v hv).trans initial

/-- Integer winding is read solely from initial data. Its conservation on
the material evolution supplies the signed-turn input on positive times. -/
theorem multi_integer_initial_product (hf : c.IsNormalFEF)
    (spd : ContinuousOn (fun q : ℝ×ℝ=>speed (c.position q.1) q.2) (Ici 0×ˢuniv))
    (curv : ContinuousOn (fun q : ℝ×ℝ=>curvature (c.position q.1) q.2) (Ici 0×ˢuniv))
    (product : ContinuousWithinAt (fun t=>2*c.bending t*c.coreLength t) (Ici 0) 0)
    {n : ℤ} (hm : 2≤|(n:ℝ)|) (turn : c.signedCurvatureIntegral 0=(n:ℝ)*(2*Real.pi))
    (initial : 2*c.bending 0*c.coreLength 0≤(2*Real.pi*|(n:ℝ)|)^2+Real.pi^2/4) :
    ∀v,0<v → 2*c.bending v*c.coreLength v≤2*c.bending 0*c.coreLength 0 := by
  apply c.multi_bending_product_from_zero hf hm product _ initial
  intro v hv
  rw [c.multi_turn_from_zero spd curv turn hv.le,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi),mul_comm]

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.multi_integer_initial_product
