import LengthGrowth.ActualFlow.CubicHalfThreshold

/-! Dissipation and macroscopic turning at genuine positive-time maxima
of the energy-length product, including a logarithmic failure of the
sharp upper length estimate. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem dissipation_at_product_record (hf : c.IsNormalFEF) {t : ℝ} (ht : 0<t)
    (record : ∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) :
    4*(c.dissipation t*c.length t^2/(8*c.energy t^3))≤1 := by
  have slopes := (hasDerivAt_iff_tendsto_slope_left_right.mp (c.normalizedProduct_hasDerivAt_normal hf ht)).1
  have rate : 0≤c.energy t*c.lengthRate t-c.length t*c.dissipation t := by
    apply ge_of_tendsto slopes
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Ioi_mem_nhds ht)] with x hx hxp
    rw [slope_def_field]
    exact div_nonneg_of_nonpos (sub_nonpos.mpr (record x ⟨hxp.le,hx.le⟩)) (sub_nonpos.mpr hx.le)
  have ep:=c.energy_pos ht.le
  have lp:=c.length_pos ht.le
  have dn:=c.dissipation_nonneg t
  have sq:=pow_le_pow_left₀ (mul_nonneg lp.le dn) (sub_nonneg.mp rate) 2
  have v:=c.lengthRate_sq_le ht.le
  rcases eq_or_lt_of_le dn with hz|dp
  · rw [←hz]
    norm_num
  · have lower : c.dissipation t*c.length t^2≤2*c.energy t^3 := by
      apply (mul_le_mul_iff_left₀ dp).mp
      nlinarith only [sq,mul_le_mul_of_nonneg_left v (sq_nonneg (c.energy t))]
    field_simp [ep.ne']
    nlinarith only [lower]

/-- The count need not be continuous or measurable in time. Its only
input is a static lower bound on those slices with d≤1/4. -/
private theorem root_count {u d C m : ℝ} (up : 0<u) (hC : 0<C) (hm : 0≤m)
    (hd : 4*d≤1) (hs : (2*u)^2≤C*m^6*d) : (16/C)^(1/6:ℝ)*u^(1/3:ℝ)≤m := by
  have total:16*u^2≤C*m^6 := by
    nlinarith only [hs,mul_le_mul_of_nonneg_left hd (mul_nonneg hC.le (by positivity : 0≤m^6))]
  have base : 16/C*u^2≤m^6 := by
    field_simp [hC.ne']
    linarith only [total]
  have coef:= Real.rpow_le_rpow (show 0≤16/C*u^2 by positivity) base (by norm_num : (0:ℝ)≤1/6)
  rw [Real.mul_rpow (by positivity : 0≤(16:ℝ)/C) (sq_nonneg u),←Real.rpow_natCast u 2,
    ←Real.rpow_mul up.le,←Real.rpow_natCast m 6,←Real.rpow_mul hm] at coef
  norm_num at coef
  exact coef

/-- The static theorem need only supply an actual family of disjoint
arcs on each low-dissipation slice. No measurable selection is used. -/
theorem macroscopic_witness_at_high_records (hf : c.IsNormalFEF) (fail : ¬c.HasQuarterLengthBound)
    {R : PeriodicRegularPosition→ℕ→Prop} {C : ℝ} (hC : 0<C)
    (force : ∀t,(ht:0<t) → let d:=c.dissipation t*c.length t^2/(8*c.energy t^3)
      4*d≤1 → ∃m : ℕ,R (c.regularPositionAt ht.le) m ∧ (2*c.normalizedProduct t)^2≤C*(m:ℝ)^6*d)
    (T M : ℝ) :
    ∃ t, ∃ ht : 0<t, T<t ∧ M<c.normalizedProduct t ∧
      (∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
      ∃ m : ℕ,R (c.regularPositionAt ht.le) m ∧
        (16/C)^(1/6:ℝ)*c.normalizedProduct t^(1/3:ℝ)≤(m:ℝ) := by
  obtain ⟨t,ltT,tp,hi,rec,_⟩:=c.high_record_cubic_half_of_failure hf fail M T
  have hd:=c.dissipation_at_product_record hf tp rec
  obtain ⟨m,occ,hs⟩:=force t tp hd
  exact ⟨t,tp,ltT,hi,rec,m,occ,root_count (mul_pos (c.energy_pos tp.le)
    (c.length_pos tp.le)) hC (by positivity) hd hs⟩

theorem macroscopic_count_at_high_records (hf : c.IsNormalFEF) (fail : ¬c.HasQuarterLengthBound)
    {m : ℝ→ℝ} {C : ℝ} (hC : 0<C) (hm : ∀t>0,0≤m t)
    (force : ∀t>0,let d:=c.dissipation t*c.length t^2/(8*c.energy t^3)
      4*d≤1 → (2*c.normalizedProduct t)^2≤C*(m t)^6*d) (T M : ℝ) :
    ∃ t, T<t ∧ 0<t ∧ M<c.normalizedProduct t ∧
      (∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
      (16/C)^(1/6:ℝ)*c.normalizedProduct t^(1/3:ℝ)≤m t := by
  obtain ⟨t,ltT,tp,hi,rec,_⟩:=c.high_record_cubic_half_of_failure hf fail M T
  have hd:=c.dissipation_at_product_record hf tp rec
  exact ⟨t,ltT,tp,hi,rec,root_count (mul_pos (c.energy_pos tp.le)
    (c.length_pos tp.le)) hC (hm t tp) hd (force t tp hd)⟩

theorem quarter_bound_of_small_macroscopic_count (hf : c.IsNormalFEF)
    {m : ℝ→ℝ} {C T M : ℝ} (hC : 0<C) (hm : ∀t>0,0≤m t)
    (force : ∀t>0,let d:=c.dissipation t*c.length t^2/(8*c.energy t^3)
      4*d≤1 → (2*c.normalizedProduct t)^2≤C*(m t)^6*d)
    (small : ∀t>T,M<c.normalizedProduct t →
      m t<(16/C)^(1/6:ℝ)*c.normalizedProduct t^(1/3:ℝ)) : c.HasQuarterLengthBound := by
  by_contra fail
  obtain ⟨t,ht,_,hi,_,large⟩:=c.macroscopic_count_at_high_records hf fail hC hm force T M
  exact (not_lt_of_ge large) (small t ht hi)

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.dissipation_at_product_record
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_bound_of_small_macroscopic_count
