import Migration.SublevelSpatialRate
import Migration.SublevelMaterialCurve

noncomputable section
open Set MeasureTheory
namespace MigrationGeometry.Flow.SmoothPeriodicImmersion
variable {I : Set ℝ} (c : SmoothPeriodicImmersion I)

private theorem physical_product_derivative (hf : c.IsNormalFEF) {v : ℝ} (hv : v∈I) :
    let p := (c.materialSlice hv).bendingCurve
    HasDerivAt (fun t=>2*c.bending t*c.coreLength t)
      (2*(p.energy*(∫u in 0..p.period,p.curvature u*p.force u)-p.period*p.dissipation)) v := by
  let H : ℂ →L[ℝ] ℝ := 0
  have hlen (t : ℝ) : c.cutoffMass H (fun _=>1) t=c.coreLength t := by simp [cutoffMass,coreLength]
  have dl := c.cutoffMass_hasDerivAt hf H (fun _=>1) (fun _=>0)
      (fun u=>hasDerivAt_const u (1:ℝ)) continuous_const hv
  rw [funext hlen] at dl
  have ll : HasDerivAt c.coreLength
      (∫u in 0..c.period,curvature (c.position v) u*force (c.position v) u*speed (c.position v) u) v := by
    simpa [cutoffMassRate] using dl
  have de := c.bending_hasDerivAt_dissipation hf H hv
  dsimp only
  apply (((de.const_mul 2).mul ll)).congr_deriv
  rw [PeriodicRegularPosition.bendingCurve_lengthRate, PeriodicRegularPosition.bendingCurve_dissipation,
    PeriodicRegularPosition.bendingCurve_energy]
  simp only [materialSlice,localDissipation,one_mul]
  change _ = 2 * (c.bending v * _ - c.coreLength v * _)
  ring

/-- The physical normalized bending energy stays below its initial threshold
on a compact forward interval, even when it starts on that threshold. -/
theorem bending_sublevel_from_initial (hf : c.IsNormalFEF) {s t C : ℝ}
    (_st : s≤t) (slab : Icc s t⊆I) (above : 4*Real.pi^2<C)
    (cap : C≤4*Real.pi^2+36) (initial : 2*c.bending s*c.coreLength s≤C) :
    ∀v∈Icc s t,2*c.bending v*c.coreLength v≤C := by
  let U := fun v=>2*c.bending v*c.coreLength v
  let S := U ⁻¹' Iic C
  have cont (v) (hv : v∈Icc s t) : ContinuousAt U v := (c.physical_product_derivative hf (slab hv)).continuousAt
  have cc : ContinuousOn U (Icc s t) := fun v hv=>(cont v hv).continuousWithinAt
  have closed : IsClosed (S∩Icc s t) := by
    rw [inter_comm]
    exact cc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have barrier := closed.Icc_subset_of_forall_mem_nhdsWithin (show s∈S from initial) (by
    intro v h
    have hv : v∈Icc s t := ⟨h.2.1,h.2.2.le⟩
    have inside : U v≤C := h.1
    rcases lt_or_eq_of_le inside with strict|eq
    · exact Filter.mem_of_superset ((cont v hv).continuousWithinAt.eventually_lt_const strict)
        (fun y hy=>show U y≤C from le_of_lt hy)
    · let p := c.materialSlice (slab hv)
      have en : p.bendingCurve.energy=c.bending v := p.bendingCurve_energy
      have leq : p.bendingCurve.period=c.coreLength v := rfl
      have up : 2*p.bendingCurve.energy*p.bendingCurve.period=C := by rw [en,leq]; exact eq
      have strict := p.bendingCurve.bending_sublevel_strict (up ▸ above) (up ▸ cap)
      have rate := c.physical_product_derivative hf (slab hv)
      have neg := ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl v)).mp
        (rate.hasDerivWithinAt (s:=Ioi v))).eventually_lt_const (show
          2*(p.bendingCurve.energy*(∫u in 0..p.bendingCurve.period,p.bendingCurve.curvature u*p.bendingCurve.force u)-
          p.bendingCurve.period*p.bendingCurve.dissipation)<0 by linarith)
      filter_upwards [self_mem_nhdsWithin,neg] with y hy n
      rw [slope_def_field] at n
      have hh := (div_lt_iff₀ (sub_pos.mpr hy)).mp n
      change U y-U v<0*(y-v) at hh
      exact show U y≤C by linarith)
  exact fun _ hv=>barrier hv

end MigrationGeometry.Flow.SmoothPeriodicImmersion
#print axioms MigrationGeometry.Flow.SmoothPeriodicImmersion.bending_sublevel_from_initial
