import LengthGrowth.ActualFlow.CriticalDensityRate

/-! Physical-time consequences of a positive power of the normalized
energy controlled by the logarithmic drop in bending energy. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

theorem log_inverse_energy_bound (hf : c.IsNormalFEF) :
    ∃ A : ℝ, ∀ t≥0, -Real.log (c.energy t)≤A+Real.log (1+t) := by
  let A := c.length 0+c.energy 0+1
  have l₀ := c.length_pos (t:=0) le_rfl
  have e₀ := c.energy_pos (t:=0) le_rfl
  have ha : 0<A := by dsimp [A]; linarith
  refine ⟨Real.log A,fun t ht => ?_⟩
  have he:=c.energy_pos ht
  have hgeom:=c.sharp_energy_length ht
  have unit : 1≤c.energy t*c.length t := by nlinarith only [hgeom,Real.pi_gt_three]
  have il : (c.energy t)⁻¹≤c.length t := by
    rw [inv_eq_one_div,div_le_iff₀ he]
    linarith only [unit]
  have cap : c.length t≤A*(1+t) := by
    have h:=c.secant_sq_le_energy_drop hf (s:=0) le_rfl ht
    simp only [sub_zero] at h
    by_contra! bad
    have more : c.energy 0*(1+t)<c.length t-c.length 0 := by
      dsimp only [A] at bad
      nlinarith only [bad,mul_nonneg l₀.le ht,ht]
    have sq:=mul_self_lt_mul_self (by positivity : 0≤c.energy 0*(1+t)) more
    nlinarith only [sq,h,mul_nonneg ht (sq_nonneg (c.energy t)),
      mul_nonneg ht (sq_nonneg (c.energy 0)),sq_nonneg (c.energy 0*t),sq_nonneg (c.energy 0)]
  simpa only [Real.log_inv,Real.log_mul ha.ne' (by positivity : 1+t≠0)] using
    Real.log_le_log (inv_pos.mpr he) (il.trans cap)

private theorem product_envelope (hf : c.IsNormalFEF) {T q K : ℝ}
    (hT : 0≤T) (hq : 0<q) (hK : 0≤K)
    (bar : AntitoneOn (fun t=>c.normalizedProduct t^q+K*Real.log (c.energy t)) (Ici T)) :
    ∃ B : ℝ, 0<B ∧ ∀t≥T, Real.sqrt (c.normalizedProduct t) ≤
      B*(1+Real.log (1+t))^(1/(2*q)) := by
  obtain ⟨A,ecap⟩:=c.log_inverse_energy_bound hf
  let V := c.normalizedProduct T^q+K*(Real.log (c.energy T)+A)
  let H := |V|+K+1
  let β := 1/(2*q)
  have hh : 0<H := by dsimp [H]; positivity
  have hb : 0<β := by dsimp [β]; positivity
  refine ⟨H^β,Real.rpow_pos_of_pos hh _,fun t ht=>?_⟩
  have t0:=hT.trans ht
  have ul:=c.normalizedProduct_nonneg t
  have comp:=bar (Set.mem_Ici.mpr (le_rfl : T≤T)) (Set.mem_Ici.mpr ht) ht
  have el:=mul_le_mul_of_nonneg_left (ecap t t0) hK
  have logp:=Real.log_nonneg (show 1≤1+t by linarith)
  have v : c.normalizedProduct t^q≤V+K*Real.log (1+t) := by dsimp [V]; linarith
  have bound : c.normalizedProduct t^q≤H*(1+Real.log (1+t)) := by
    dsimp [H]
    nlinarith only [v,le_abs_self V,mul_nonneg (abs_nonneg V) logp,hK,logp]
  have raised:=Real.rpow_le_rpow (Real.rpow_nonneg ul q) bound hb.le
  rw [←Real.rpow_mul ul,show q*β=1/2 by dsimp [β]; field_simp,
    ←Real.sqrt_eq_rpow,Real.mul_rpow hh.le (by linarith : 0≤1+Real.log (1+t))] at raised
  exact raised

theorem half_length_product (hf : c.IsNormalFEF) {T t : ℝ}
    (hT : 0≤T) (ht : T≤t) (high : 2*c.length T<c.length t) :
    ∃ s∈Icc T t, c.length t≤2*fourthRoot (1+t)*Real.sqrt (c.normalizedProduct s) := by
  have ht0:=hT.trans ht
  have hh : c.length t/2∈Icc (c.length T) (c.length t) :=
    ⟨by linarith,by linarith [c.length_pos ht0]⟩
  obtain ⟨s,hst,heq⟩:=intermediate_value_Icc ht
    (c.length_continuousOn.mono (fun _ hx => hT.trans hx.1)) hh
  have hs0:=hT.trans hst.1
  have hsec:=c.secant_sq_le_energy_drop hf hs0 hst.2
  have h₁ : c.length s^2≤t*c.energy s^2 := by
    nlinarith only [heq,hsec,mul_nonneg (sub_nonneg.mpr hst.2) (sq_nonneg (c.energy t)),
      mul_nonneg hs0 (sq_nonneg (c.energy s)),congrArg (fun a:ℝ=>a^2) heq]
  have h₄ : c.length s^4≤(1+t)*(c.normalizedProduct s)^2 := by
    unfold normalizedProduct
    nlinarith only [mul_le_mul_of_nonneg_right h₁ (sq_nonneg (c.length s)),sq_nonneg (c.energy s*c.length s)]
  have hp : c.length s≤fourthRoot (1+t)*Real.sqrt (c.normalizedProduct s) := by
    by_contra! bad
    have power:=pow_lt_pow_left₀ bad (mul_nonneg (fourthRoot_nonneg _) (Real.sqrt_nonneg _)) (by decide : 4≠0)
    rw [mul_pow,fourthRoot_pow_four (by linarith)] at power
    rw [show Real.sqrt (c.normalizedProduct s)^4=c.normalizedProduct s^2 by
      rw [show (4:Nat)=2*2 from rfl,pow_mul,Real.sq_sqrt (c.normalizedProduct_nonneg s)]] at power
    exact (not_lt_of_ge h₄) power
  exact ⟨s,hst,by linarith⟩

private theorem barrier_energy_zero (hf : c.IsNormalFEF) {T q K : ℝ}
    (hT : 0≤T) (hq : 0<q) (hK : 0≤K)
    (bar : AntitoneOn (fun t=>c.normalizedProduct t^q+K*Real.log (c.energy t)) (Ici T)) :
    Tendsto c.energy atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun t => ha.trans_le (c.energy_nonneg t))
  · intro a ha
    by_contra! hn
    have lower (t:ℝ) (ht:T≤t) : a≤c.energy t := by
      by_contra! h
      apply hn
      filter_upwards [eventually_ge_atTop t] with s hst
      exact not_le.mpr ((c.energy_le_of_le hf (hT.trans ht) hst).trans_lt h)
    let V:=c.normalizedProduct T^q+K*(Real.log (c.energy T)-Real.log a)
    have cap (t:ℝ) (ht:T≤t) : c.normalizedProduct t≤V^q⁻¹ := by
      have h1:=bar (Set.mem_Ici.mpr (le_rfl : T≤T)) (Set.mem_Ici.mpr ht) ht
      have h2:=mul_le_mul_of_nonneg_left (Real.log_le_log ha (lower t ht)) hK
      have h3 : c.normalizedProduct t^q≤V := by dsimp only [V]; linarith
      simpa only [Real.rpow_rpow_inv (c.normalizedProduct_nonneg t) hq.ne'] using
        Real.rpow_le_rpow (Real.rpow_nonneg (c.normalizedProduct_nonneg t) q) h3 (inv_nonneg.mpr hq.le)
    obtain ⟨u,_,hu⟩:=isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
      (c.normalizedProduct_continuousOn.mono (fun _ hx=>hx.1))
    have hb : c.HasBoundedEnergyLength := by
      refine ⟨max (c.normalizedProduct u) (V^q⁻¹),fun t ht=>?_⟩
      by_cases h:t≤T
      · exact (hu ⟨ht,h⟩).trans (le_max_left _ _)
      · exact (cap t (le_of_not_ge h)).trans (le_max_right _ _)
    obtain ⟨C,hC,upper⟩:=c.quarter_energy_of_quarter_length hf ((c.quarter_length_iff_bounded_energyLength hf).mpr hb)
    have grow : Tendsto (fun t:ℝ=>fourthRoot (1+t)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id))
    obtain ⟨t,ht,hh⟩:=((eventually_ge_atTop T).and (grow.eventually_gt_atTop (C/a))).exists
    have pos:0<fourthRoot (1+t):=(div_pos hC ha).trans hh
    have h1:=(le_div_iff₀ pos).mp (upper t (hT.trans ht))
    have h2:=(div_lt_iff₀ ha).mp hh
    nlinarith only [h1,h2,mul_le_mul_of_nonneg_right (lower t ht) pos.le]

theorem length_energy_of_power_deficit (hf : c.IsNormalFEF) {T q H U₀ : ℝ}
    (hT : 0≤T) (hq : 0<q) (hH : 0≤H)
    (high : ∀t>T,U₀≤c.normalizedProduct t →
      c.normalizedProduct t^q*(Real.sqrt (c.normalizedProduct t)-c.stressScale t) ≤ H*Real.sqrt (c.normalizedProduct t)) :
    (∃ B : ℝ, 0<B ∧ ∀t≥T, c.length t≤B*fourthRoot (1+t)*(1+Real.log (1+t))^(1/(2*q))) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  obtain ⟨K,hK,bar⟩:=c.density_log_barrier hf hT hq hH high
  refine ⟨?_,c.barrier_energy_zero hf hT hq hK bar⟩
  obtain ⟨B,hB,cap⟩:=c.product_envelope hf hT hq hK bar
  let C:=2*(B+c.length T)
  have hl:=c.length_pos hT
  have cp : 0<C := by dsimp [C]; positivity
  refine ⟨C,cp,fun t ht=>?_⟩
  have t0:=hT.trans ht
  have rt : 1≤fourthRoot (1+t) := by simpa [fourthRoot] using fourthRoot_mono (show (1:ℝ)≤1+t by linarith)
  have lp:=Real.log_nonneg (show 1≤1+t by linarith)
  have β : 0≤1/(2*q) := by positivity
  have gp:=Real.one_le_rpow (show 1≤1+Real.log (1+t) by linarith) β
  rcases le_or_gt (c.length t) (2*c.length T) with low|large
  · calc
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C*fourthRoot (1+t) := by nlinarith only [mul_nonneg cp.le (sub_nonneg.mpr rt)]
      _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg cp.le (fourthRoot_nonneg (1+t))) (sub_nonneg.mpr gp)]
  · obtain ⟨s,st,half⟩:=c.half_length_product hf hT ht large
    have sp : 0≤1+Real.log (1+s) := by linarith [Real.log_nonneg (show 1≤1+s by linarith [st.1])]
    have mono:=Real.rpow_le_rpow sp (show 1+Real.log (1+s)≤1+Real.log (1+t)
      from add_le_add_right (Real.log_le_log (by linarith [st.1]) (by linarith [st.2])) 1) β
    have upper:=(cap s st.1).trans (mul_le_mul_of_nonneg_left mono hB.le)
    dsimp only [C]
    nlinarith only [half,mul_le_mul_of_nonneg_left upper (mul_nonneg (by norm_num : (0:ℝ)≤2) (fourthRoot_nonneg (1+t))),
      mul_nonneg (mul_nonneg hl.le (fourthRoot_nonneg (1+t))) (zero_le_one.trans gp)]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.length_energy_of_power_deficit
