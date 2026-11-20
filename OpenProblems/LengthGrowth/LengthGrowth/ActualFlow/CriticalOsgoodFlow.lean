import LengthGrowth.ActualFlow.CriticalEndpointFlow

/-! An unbounded primitive in the energy-length variable forces energy
decay under weighted critical curvature-reversal bounds. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem energy_zero_of_unbounded_primitive (hf : c.IsNormalFEF)
    {T C : ℝ} (hT : 0≤T) (hC : 0≤C) {F : ℝ→ℝ}
    (grow : Tendsto F atTop atTop)
    (bar : ∃ B : ℝ, ∀t≥T, F (c.normalizedProduct t)+C*Real.log (c.energy t)≤B) :
    Tendsto c.energy atTop (𝓝 0) := by
  obtain ⟨B,bar⟩:=bar
  apply tendsto_order.2
  constructor
  · exact fun a ha => Eventually.of_forall fun t => ha.trans_le (c.energy_nonneg t)
  · intro a ha
    by_contra! bad
    have lower (t : ℝ) (ht : T≤t) : a≤c.energy t := by
      by_contra! small
      apply bad
      filter_upwards [eventually_ge_atTop t] with s hst
      exact not_le.mpr ((c.energy_le_of_le hf (hT.trans ht) hst).trans_lt small)
    obtain ⟨M,hM⟩:=eventually_atTop.1 (grow.eventually_gt_atTop (B-C*Real.log a))
    have cap (t:ℝ) (ht:T≤t) : c.normalizedProduct t≤M := by
      by_contra! hi
      linarith only [bar t ht,hM _ hi.le,
        mul_le_mul_of_nonneg_left (Real.log_le_log ha (lower t ht)) hC]
    obtain ⟨s,_,maximum⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
      (c.normalizedProduct_continuousOn.mono (fun _ hs=>hs.1))
    have bd : c.HasBoundedEnergyLength := by
      refine ⟨max M (c.normalizedProduct s),fun t ht=>?_⟩
      rcases le_total T t with h|h
      · exact (cap t h).trans (le_max_left ..)
      · exact (maximum ⟨ht,h⟩).trans (le_max_right ..)
    obtain ⟨H,hH,upper⟩:=c.quarter_energy_of_quarter_length hf
      ((c.quarter_length_iff_bounded_energyLength hf).mpr bd)
    have gt : Tendsto (fun t:ℝ=>fourthRoot (1+t)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id))
    obtain ⟨t,ht,high⟩:=((eventually_ge_atTop T).and (gt.eventually_gt_atTop (H/a))).exists
    have pos:0<fourthRoot (1+t):=(div_pos hH ha).trans high
    have up:=(le_div_iff₀ pos).mp (upper t (hT.trans ht))
    have low:=(div_lt_iff₀ ha).mp high
    nlinarith only [up,low,mul_le_mul_of_nonneg_right (lower t ht) pos.le]

/-- The material count is allowed to exceed the cube-root rate by b(U).
An unbounded primitive of 1/(U*b(U)^3) suffices. -/
theorem energy_zero_of_osgood_half_rms_index (hf : c.IsNormalFEF) {T B U₀ : ℝ}
    (hT : 0≤T) (hB : 0≤B) {b F : ℝ→ℝ}
    (hb : ∀u>1, 1≤b u) (grow : Tendsto F atTop atTop)
    (derF : ∀u>1, HasDerivAt F (1/(u*(b u)^3)) u)
    (count : ∀t,(ht:T<t) → U₀≤c.normalizedProduct t →
      ((c.regularPositionAt (hT.trans ht.le)).criticalDensityIndex:ℝ)+1≤
        B*c.normalizedProduct t^(1/3:ℝ)*b (c.normalizedProduct t)) :
    Tendsto c.energy atTop (𝓝 0) := by
  let U:=c.normalizedProduct
  let K:=max (max 2 ((10^8:ℝ)*B^3)) (Real.sqrt U₀)
  have ku : 0≤K := (by norm_num : (0:ℝ)≤2).trans ((le_max_left ..).trans (le_max_left ..))
  have uu (t:ℝ) (ht:0≤t) : 1<U t := by
    have h:=c.sharp_energy_length ht
    change 1<c.energy t*c.length t
    nlinarith only [h,Real.pi_gt_three,sq_nonneg (Real.pi-3)]
  have stress (t:ℝ) (ht:T<t) : Real.sqrt (U t) ≤ K*b (U t)^3*c.stressScale t := by
    have t0:=hT.trans ht.le
    have bb:=hb _ (uu t t0)
    have bk : 1≤b (U t)^3 := one_le_pow₀ bb
    have z := (c.density_stress_control t0).1
    have non : 0≤b (U t) := zero_le_one.trans bb
    by_cases hi : U₀≤U t
    · let p:=c.regularPositionAt t0
      have ct : (p.criticalDensityIndex:ℝ)+1≤(B*b (U t))*(U t)^(1/3:ℝ) := by
        simpa only [mul_right_comm] using count t ht hi
      have sf:=c.stress_fraction_of_half_rms_count t0 (mul_nonneg hB non) p.criticalDensityIndex
        p.criticalDensityIndex_spec ct
      apply sf.trans (mul_le_mul_of_nonneg_right _ (zero_le_one.trans z))
      apply max_le
      · have k2 : 2≤K := (le_max_left ..).trans (le_max_left ..)
        nlinarith only [k2,mul_nonneg ku (sub_nonneg.mpr bk)]
      · have kk : (10^8:ℝ)*B^3≤K := (le_max_right ..).trans (le_max_left ..)
        rw [mul_pow]
        nlinarith only [mul_le_mul_of_nonneg_right kk (pow_nonneg non 3)]
    · have lo := Real.sqrt_le_sqrt (le_of_not_ge hi)
      have sk : Real.sqrt U₀≤K := le_max_right ..
      apply (lo.trans sk).trans
      nlinarith only [mul_nonneg ku (sub_nonneg.mpr bk), mul_nonneg (mul_nonneg ku (pow_nonneg non 3)) (sub_nonneg.mpr z)]
  let W:=fun t=>F (U t)+K*Real.log (c.energy t)
  have sub : Ici T⊆Ici 0 := fun _ ht=>hT.trans ht
  have cF : ContinuousOn F (Ioi 1) := fun u hu=>(derF u hu).continuousAt.continuousWithinAt
  have cw : ContinuousOn W (Ici T) := (cF.comp (c.normalizedProduct_continuousOn.mono sub)
    (fun x hx=>uu x (sub hx))).add ((c.log_energy_continuousOn.mono sub).const_mul K)
  have dw (t:ℝ) (ht:T<t) : HasDerivAt W
      ((1/(U t*b (U t)^3))*(c.energy t*c.lengthRate t-c.length t*c.dissipation t)
       +K*(-c.dissipation t/c.energy t)) t := by
    have t0:=hT.trans_lt ht
    exact ((derF _ (uu t t0.le)).comp t (c.normalizedProduct_hasDerivAt_normal hf t0)).add
      (((c.energy_hasDerivAt_normal hf t0).log (c.energy_pos t0.le).ne').const_mul K)
  have mono : AntitoneOn W (Ici T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _) cw
    · rw [interior_Ici]
      exact fun t ht=>(dw t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [(dw t ht).deriv]
      have t0:=hT.trans ht.le
      obtain ⟨hz,vel⟩:=c.density_stress_control t0
      have ep:=c.energy_pos t0
      have lp:=c.length_pos t0
      have bp:0<b (U t) := zero_lt_one.trans_le (hb _ (uu t t0))
      have dl:=mul_nonneg (c.dissipation_nonneg t) lp.le
      have sc:=mul_le_mul_of_nonneg_left (stress t ht) dl
      have rate : c.energy t*c.lengthRate t≤K*b (U t)^3*(c.dissipation t*c.length t) := by
        by_contra! bad
        change c.energy t*c.lengthRate t*c.stressScale t≤_ * Real.sqrt (U t) at vel
        nlinarith only [vel,sc,mul_pos (sub_pos.mpr bad) (zero_lt_one.trans_le hz)]
      have up:=zero_lt_one.trans (uu t t0)
      field_simp [up.ne',bp.ne',ep.ne']
      dsimp only [U,normalizedProduct] at rate ⊢
      nlinarith only [mul_le_mul_of_nonneg_left rate ep.le,mul_nonneg ep.le dl]
  exact c.energy_zero_of_unbounded_primitive hf hT ku grow
    ⟨W T,fun t ht=>mono (mem_Ici.mpr (le_refl T)) (mem_Ici.mpr ht) ht⟩

/-- The logarithmic endpoint has primitive log(1+log U). -/
theorem energy_zero_of_log_critical_half_rms_index (hf : c.IsNormalFEF) {T B U₀ : ℝ}
    (hT : 0≤T) (hB : 0≤B)
    (count : ∀t,(ht:T<t) → U₀≤c.normalizedProduct t →
      ((c.regularPositionAt (hT.trans ht.le)).criticalDensityIndex:ℝ)+1≤
        B*c.normalizedProduct t^(1/3:ℝ)*(1+Real.log (c.normalizedProduct t))^(1/3:ℝ)) :
    Tendsto c.energy atTop (𝓝 0) := by
  apply c.energy_zero_of_osgood_half_rms_index hf hT hB (F:=fun u=>Real.log (1+Real.log u))
    (b:=fun u=>(1+Real.log u)^(1/3:ℝ)) (U₀:=U₀) _ _ _ count
  · intro u hu
    exact Real.one_le_rpow (by linarith [Real.log_pos hu]) (by norm_num)
  · exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ _ Real.tendsto_log_atTop)
  · intro u hu
    have up:=zero_lt_one.trans hu
    have lp : 0<1+Real.log u := by linarith [Real.log_pos hu]
    rw [←Real.rpow_natCast ((1+Real.log u)^(1/3:ℝ)) 3,←Real.rpow_mul lp.le]
    norm_num
    convert (((Real.hasDerivAt_log up.ne').const_add 1).log lp.ne') using 1
    field_simp

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.energy_zero_of_osgood_half_rms_index
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.energy_zero_of_log_critical_half_rms_index
