import LengthGrowth.ActualFlow.CriticalDensityTime

/-! Subcritical excursion density with no fixed power gap. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A large-product logarithmic slope estimate controls the entire tail,
including repeated downward and upward crossings of its slice threshold. -/
theorem high_slice_log_envelope (hf : c.IsNormalFEF) {T η U₀ : ℝ}
    (hT : 0≤T) (he : 0≤η) (high : ∀t>T, U₀≤c.normalizedProduct t →
      Real.sqrt (c.normalizedProduct t) ≤ (1+η)*c.stressScale t) :
    ∃ B : ℝ, ∀t≥T, Real.log (c.normalizedProduct t)+η*Real.log (c.energy t) ≤ B := by
  let U := c.normalizedProduct
  let W := fun t => Real.log (U t)+η*Real.log (c.energy t)
  let M := max (U T) U₀
  have pos (s : ℝ) (hs : 0≤s) : 0<U s := mul_pos (c.energy_pos hs) (c.length_pos hs)
  refine ⟨Real.log M+η*Real.log (c.energy T),fun t ht=>?_⟩
  let good := {s∈Icc T t | U s≤M}
  have cut : IsCompact good := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.isClosed_le (c.normalizedProduct_continuousOn.mono (fun _ hs => hT.trans hs.1))
      continuousOn_const) (fun _ hs=>hs.1)
  have ne : good.Nonempty := ⟨T,⟨le_rfl,ht⟩,le_max_left ..⟩
  obtain ⟨s,hs,last⟩ := cut.exists_isMaxOn ne continuous_id.continuousOn
  have hsT : T≤s := hs.1.1
  have hst : s≤t := hs.1.2
  have later (x : ℝ) (hx : x∈Ioo s t) : U₀≤U x := by
    apply (le_max_right (U T) U₀).trans
    by_contra! low
    exact (not_le.mpr hx.1) (last (show x∈good from ⟨⟨hsT.trans hx.1.le,hx.2.le⟩,low.le⟩))
  have sub : Icc s t ⊆ Ici 0 := fun _ hh => (hT.trans hsT).trans hh.1
  have cont : ContinuousOn W (Icc s t) :=
    ((c.normalizedProduct_continuousOn.mono sub).log (fun x hx => (pos x (sub hx)).ne')).add
      ((c.log_energy_continuousOn.mono sub).const_mul η)
  have derivW (x : ℝ) (hx : x∈Ioo s t) : HasDerivAt W
      ((c.energy x*c.lengthRate x-c.length x*c.dissipation x)/U x+
        η*(-c.dissipation x/c.energy x)) x := by
    have ht0 := (hT.trans hsT).trans_lt hx.1
    exact ((c.normalizedProduct_hasDerivAt_normal hf ht0).log (pos x ht0.le).ne').add
      (((c.energy_hasDerivAt_normal hf ht0).log (c.energy_pos ht0.le).ne').const_mul η)
  have mono : AntitoneOn W (Icc s t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) cont
    · rw [interior_Icc]
      intro x hx
      exact (derivW x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(derivW x hx).deriv]
      have xx:=hsT.trans_lt hx.1
      have x0:=hT.trans xx.le
      obtain ⟨hz,vel⟩:=c.density_stress_control x0
      have zz : 0<c.stressScale x := zero_lt_one.trans_le hz
      have dl := mul_nonneg (c.dissipation_nonneg x) (c.length_pos x0).le
      have more := mul_le_mul_of_nonneg_left (high x xx (later x hx)) dl
      have rate : c.energy x*c.lengthRate x ≤ (1+η)*(c.dissipation x*c.length x) := by
        by_contra! bad
        nlinarith only [mul_pos (sub_pos.mpr bad) zz,vel,more]
      change (c.energy x*c.lengthRate x-c.length x*c.dissipation x)/(c.energy x*c.length x)+_≤0
      have ep:=c.energy_pos x0
      have lp:=c.length_pos x0
      field_simp [ep.ne',lp.ne']
      nlinarith only [rate]
  have drop := mono (show s∈Icc s t from ⟨le_rfl,hst⟩) (show t∈Icc s t from ⟨hst,le_rfl⟩) hst
  have lo := Real.log_le_log (pos s (hT.trans hsT)) hs.2
  have en := mul_le_mul_of_nonneg_left (Real.log_le_log (c.energy_pos (hT.trans hsT))
    (c.energy_le_of_le hf hT hsT)) he
  exact drop.trans (add_le_add lo en)

private theorem log_envelope_energy_zero (hf : c.IsNormalFEF) {T B : ℝ} (hT : 0≤T)
    (bar : ∀ t≥T, Real.log (c.normalizedProduct t)+Real.log (c.energy t)≤B) :
    Tendsto c.energy atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun t => ha.trans_le (c.energy_nonneg t)
  · intro a ha
    by_contra! hn
    have lower (t : ℝ) (ht : T≤t) : a≤c.energy t := by
      by_contra! h
      apply hn
      filter_upwards [eventually_ge_atTop t] with s hst
      exact not_le.mpr ((c.energy_le_of_le hf (hT.trans ht) hst).trans_lt h)
    have cap (t : ℝ) (ht : T≤t) : c.normalizedProduct t≤Real.exp (B-Real.log a) := by
      have ep := Real.log_le_log ha (lower t ht)
      have up : 0<c.normalizedProduct t := mul_pos (c.energy_pos (hT.trans ht)) (c.length_pos (hT.trans ht))
      rw [←Real.exp_log up]
      apply Real.exp_le_exp.mpr
      linarith only [ep,bar t ht]
    obtain ⟨s,_,maximum⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT)
      (c.normalizedProduct_continuousOn.mono (fun _ hx => hx.1))
    have bounded : c.HasBoundedEnergyLength := by
      refine ⟨max (c.normalizedProduct s) (Real.exp (B-Real.log a)),fun t ht=>?_⟩
      rcases le_total t T with h|h
      · exact (maximum ⟨ht,h⟩).trans (le_max_left ..)
      · exact (cap t h).trans (le_max_right ..)
    obtain ⟨C,hC,upper⟩ := c.quarter_energy_of_quarter_length hf
      ((c.quarter_length_iff_bounded_energyLength hf).mpr bounded)
    have grow : Tendsto (fun t:ℝ=>fourthRoot (1+t)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_left _ _ tendsto_id))
    obtain ⟨t,ht,large⟩ := ((eventually_ge_atTop T).and (grow.eventually_gt_atTop (C/a))).exists
    have pos : 0<fourthRoot (1+t) := (div_pos hC ha).trans large
    have h1 := (le_div_iff₀ pos).mp (upper t (hT.trans ht))
    have h2 := (div_lt_iff₀ ha).mp large
    nlinarith only [h1,h2,mul_le_mul_of_nonneg_right (lower t ht) pos.le]

private theorem subpower_length (hf : c.IsNormalFEF) {T ε B : ℝ} (hT : 0≤T) (he : 0<ε)
    (bar : ∀ t≥T, Real.log (c.normalizedProduct t)+(2*ε)*Real.log (c.energy t)≤B) :
    ∃ C : ℝ, 0<C ∧ ∀t≥T, c.length t≤C*(1+t)^((1/4:ℝ)+ε) := by
  obtain ⟨A,en⟩ := c.log_inverse_energy_bound hf
  let K := Real.exp (B/2+ε*A)
  have kp : 0<K := Real.exp_pos _
  have prod (t : ℝ) (ht : T≤t) : Real.sqrt (c.normalizedProduct t)≤K*(1+t)^ε := by
    have t0:=hT.trans ht
    have up : 0<c.normalizedProduct t := mul_pos (c.energy_pos t0) (c.length_pos t0)
    have tp : 0<1+t := by linarith
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos up,Real.rpow_def_of_pos tp]
    change Real.exp _≤Real.exp (B/2+ε*A)*Real.exp _
    rw [←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [bar t ht,mul_le_mul_of_nonneg_left (en t t0) he.le]
  let C := 2*(K+c.length T)
  have cp : 0<C := by dsimp [C]; have := c.length_pos hT; positivity
  refine ⟨C,cp,fun t ht=>?_⟩
  have t0:=hT.trans ht
  have tp : 0<1+t := by linarith
  have power : 1≤(1+t)^((1/4:ℝ)+ε) := Real.one_le_rpow (by linarith) (by positivity)
  rcases le_or_gt (c.length t) (2*c.length T) with low|large
  · have small : c.length t≤C := by dsimp [C]; linarith only [low,kp]
    exact small.trans (by nlinarith only [mul_nonneg cp.le (sub_nonneg.mpr power)])
  · obtain ⟨s,hs,half⟩:=c.half_length_product hf hT ht large
    have cap := (prod s hs.1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith [hs.1] : 0≤1+s) (by linarith [hs.2] : 1+s≤1+t) he.le) kp.le)
    have root : fourthRoot (1+t)=(1+t)^(1/4:ℝ) := by
      rw [fourthRoot,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul tp.le]
      norm_num
    rw [root] at half
    rw [Real.rpow_add tp]
    have coef : 2*K≤C := by dsimp only [C]; linarith only [c.length_pos hT]
    calc
      c.length t ≤ 2*((1+t)^(1/4:ℝ))*(K*(1+t)^ε) :=
        half.trans (mul_le_mul_of_nonneg_left cap (by positivity))
      _ = (2*K)*((1+t)^(1/4:ℝ)*(1+t)^ε) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right coef (by positivity)

/-- A vanishing relative stress-scale deficit at large product is sufficient
for every strictly super-quarter length bound and for decay of the bending
energy. The threshold may depend arbitrarily on the requested accuracy. -/
theorem length_energy_of_subpower_deficit (hf : c.IsNormalFEF) {T : ℝ} (hT : 0≤T)
    (high : ∀η : ℝ, 0<η → ∃U₀ : ℝ, ∀t>T, U₀≤c.normalizedProduct t →
      Real.sqrt (c.normalizedProduct t)≤(1+η)*c.stressScale t) :
    (∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀t≥T, c.length t≤C*(1+t)^((1/4:ℝ)+ε)) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  constructor
  · intro ε he
    obtain ⟨M,hm⟩ := high (2*ε) (by positivity)
    obtain ⟨B,bar⟩ := c.high_slice_log_envelope hf hT (by positivity) hm
    exact c.subpower_length hf hT he bar
  · obtain ⟨M,hm⟩ := high 1 zero_lt_one
    obtain ⟨B,bar⟩ := c.high_slice_log_envelope hf hT zero_le_one hm
    exact c.log_envelope_energy_zero hf hT (fun t ht => by simpa only [one_mul] using bar t ht)

#print axioms high_slice_log_envelope
#print axioms length_energy_of_subpower_deficit

/-- On one flow violating a fixed power bound, a fixed relative deficit
recurs arbitrarily late and above every prescribed energy-length product. -/
theorem arbitrarily_late_stress_deficit_of_superquarter (hf : c.IsNormalFEF) {T ε : ℝ}
    (hT : 0≤T) (he : 0<ε)
    (fail : ¬∃C : ℝ, 0<C ∧ ∀t≥T, c.length t≤C*(1+t)^((1/4:ℝ)+ε)) :
    ∀ S≥T, ∀ M : ℝ, ∃t>S, M≤c.normalizedProduct t ∧
      (1+2*ε)*c.stressScale t < Real.sqrt (c.normalizedProduct t) := by
  intro S hs M
  by_contra! none
  obtain ⟨s,_,maximum⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hs)
    (c.normalizedProduct_continuousOn.mono (fun _ hx => hT.trans hx.1))
  let H := max M (c.normalizedProduct s+1)
  have high (t : ℝ) (ht : T<t) (hu : H≤c.normalizedProduct t) :
      Real.sqrt (c.normalizedProduct t) ≤ (1+2*ε)*c.stressScale t := by
    have late : S<t := by
      by_contra! early
      have cap := maximum (show t∈Icc T S from ⟨ht.le,early⟩)
      change c.normalizedProduct t≤c.normalizedProduct s at cap
      linarith only [cap,(le_max_right M (c.normalizedProduct s+1)).trans hu]
    exact none t late ((le_max_left M _).trans hu)
  obtain ⟨B,bar⟩ := c.high_slice_log_envelope hf hT (by positivity) high
  exact fail (c.subpower_length hf hT he bar)

#print axioms arbitrarily_late_stress_deficit_of_superquarter
end LengthGrowth.ActualFlow.ForwardImmersion
