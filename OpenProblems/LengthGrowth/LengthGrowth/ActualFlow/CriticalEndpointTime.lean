import LengthGrowth.ActualFlow.CriticalDensitySubpower

/-! Length and energy rates when the normalized stress stays bounded below
by a fixed fraction of the root energy-length product. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

private theorem length_log_cap (hf : c.IsNormalFEF) {T K : ℝ}
    (hT : 0≤T) (hK : 1≤K)
    (h : ∀t>T, Real.sqrt (c.normalizedProduct t)≤K*c.stressScale t) :
    ∃ B : ℝ, ∀t≥T, Real.log (c.length t)+K*Real.log (c.energy t)≤B := by
  obtain ⟨B,cap⟩:=c.high_slice_log_envelope hf (U₀:=0) hT (sub_nonneg.mpr hK)
    (fun t ht _ => by simpa only [add_sub_cancel] using h t ht)
  refine ⟨B,fun t ht => ?_⟩
  have hc:=cap t ht
  rw [normalizedProduct,Real.log_mul (c.energy_pos (hT.trans ht)).ne'
    (c.length_pos (hT.trans ht)).ne'] at hc
  linarith

private theorem length_rate_of_cap (hf : c.IsNormalFEF) {T K B : ℝ}
    (hT : 0≤T) (hK : 1≤K)
    (bar : ∀t≥T, Real.log (c.length t)+K*Real.log (c.energy t)≤B) :
    ∃ C : ℝ, 0<C ∧ ∀t≥T,c.length t≤C*(1+t)^(K/(2*K+2)) := by
  let C:=2*(c.length T+Real.exp (B/(K+1)))
  have CT:=c.length_pos hT
  have cpos : 0<C := by dsimp [C]; positivity
  have kp : 0<K := zero_lt_one.trans_le hK
  have k1 : 0<K+1 := by positivity
  refine ⟨C,cpos,fun t ht=>?_⟩
  have t0:=hT.trans ht
  have tp : 0<1+t := by linarith
  rcases le_or_gt (c.length t) (2*c.length T) with low | hi
  · have power:=Real.one_le_rpow (show 1≤1+t by linarith) (show 0≤K/(2*K+2) by positivity)
    have leC : c.length t≤C := by dsimp [C]; linarith [Real.exp_pos (B/(K+1))]
    exact leC.trans (by nlinarith only [mul_nonneg cpos.le (sub_nonneg.mpr power)])
  · have hh : c.length t/2∈Icc (c.length T) (c.length t) :=
      ⟨by linarith,by linarith [c.length_pos t0]⟩
    obtain ⟨s,hs,eq⟩:=intermediate_value_Icc ht
      (c.length_continuousOn.mono (fun _ hx => hT.trans hx.1)) hh
    have s0:=hT.trans hs.1
    have ls:=c.length_pos s0
    have es:=c.energy_pos s0
    have sec:=c.secant_sq_le_energy_drop hf s0 hs.2
    have sq : c.length s^2≤(1+t)*c.energy s^2 := by
      nlinarith only [sec,eq,congrArg (fun x : ℝ => x^2) eq,
        mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg (c.energy t)),
        mul_nonneg s0 (sq_nonneg (c.energy s)),sq_nonneg (c.energy s)]
    have len : c.length s≤Real.sqrt (1+t)*c.energy s := by
      by_contra! bad
      have ss:=sq_lt_sq' (by nlinarith only [ls,mul_nonneg (Real.sqrt_nonneg (1+t)) es.le]) bad
      rw [mul_pow,Real.sq_sqrt tp.le] at ss
      linarith only [ss,sq]
    have lg:=Real.log_le_log ls len
    rw [Real.log_mul (Real.sqrt_pos.mpr tp).ne' es.ne',Real.log_sqrt tp.le] at lg
    have comb : (K+1)*Real.log (c.length s)≤B+(K/2)*Real.log (1+t) := by
      nlinarith only [bar s hs.1,mul_le_mul_of_nonneg_left lg kp.le]
    have par : Real.log (c.length s)≤B/(K+1)+Real.log (1+t)*(K/(2*K+2)) := by
      field_simp [k1.ne',(show 0<2*K+2 by positivity).ne']
      linarith only [comb]
    have cap:=Real.exp_le_exp.mpr par
    rw [Real.exp_log ls, Real.exp_add,←Real.rpow_def_of_pos tp] at cap
    have hC : 2*Real.exp (B/(K+1))≤C := by dsimp [C];linarith
    nlinarith only [eq,cap,mul_le_mul_of_nonneg_right hC
      (Real.rpow_nonneg tp.le (K/(2*K+2)))]

private theorem force_ratio {K t : ℝ} (ht : 0≤t) (_hk : 0<K)
    (h : Real.sqrt (c.normalizedProduct t)≤K*c.stressScale t) :
    2*c.energy t^3≤K^2*c.dissipation t*c.length t^2 := by
  have e:=c.energy_pos ht
  have l:=c.length_pos ht
  have d:=c.dissipation_nonneg t
  have sq:=pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
  rw [Real.sq_sqrt (c.normalizedProduct_nonneg t),normalizedProduct,mul_pow,stressScale,
    Real.sq_sqrt (by positivity)] at sq
  field_simp [e.ne'] at sq
  by_contra! bad
  linarith only [bad,sq]

private theorem energy_rate_of_cap (hf : c.IsNormalFEF) {T K B : ℝ}
    (hT : 0≤T) (hK : 1≤K)
    (h : ∀t>T, Real.sqrt (c.normalizedProduct t)≤K*c.stressScale t)
    (bar : ∀t≥T, Real.log (c.length t)+K*Real.log (c.energy t)≤B) :
    ∃ C : ℝ, 0<C ∧ ∀t≥T,c.energy t≤C*(1+t)^(-(1/(2*K+2))) := by
  let q:=2*K+2
  let A:=Real.exp B
  let m:=2*q/(K^2*A^2)
  let G:ℝ→ℝ := fun t => Real.exp (-q*Real.log (c.energy t))
  have kp : 0<K:=zero_lt_one.trans_le hK
  have qp : 0<q := by dsimp [q];positivity
  have ap : 0<A := Real.exp_pos _
  have mp : 0<m := by dsimp [m]; positivity
  have gp (x:ℝ) : 0<G x := Real.exp_pos _
  have slope (x:ℝ) (hx:T<x) : m≤ G x*(q*c.dissipation x/c.energy x) := by
    have xt:=hT.trans hx.le
    have e:=c.energy_pos xt
    have l:=c.length_pos xt
    let R:=Real.exp (K*Real.log (c.energy x))
    have rp : 0<R:=Real.exp_pos _
    have cap : c.length x*R≤A := by
      have ex:=Real.exp_le_exp.mpr (bar x hx.le)
      rwa [Real.exp_add,Real.exp_log l] at ex
    have prod : G x*(c.energy x^2*R^2)=1 := by
      dsimp only [G,R]
      rw [←Real.exp_log e]
      simp only [Real.log_exp,←Real.exp_nat_mul,←Real.exp_add]
      convert Real.exp_zero using 2
      dsimp [q]
      ring
    have f:=c.force_ratio xt kp (h x hx)
    have both : 2*c.energy x*(c.energy x^2*R^2)≤K^2*c.dissipation x*A^2 := by
      calc
        _ ≤ (K^2*c.dissipation x*c.length x^2)*R^2 := by
          nlinarith only [mul_le_mul_of_nonneg_right f (sq_nonneg R)]
        _ = (K^2*c.dissipation x)*(c.length x*R)^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg l.le rp.le) cap 2)
          (mul_nonneg (sq_nonneg K) (c.dissipation_nonneg x))
    have mm:=mul_le_mul_of_nonneg_left both (gp x).le
    have red : 2*c.energy x≤G x*(K^2*c.dissipation x*A^2) := by
      calc
        _ = G x*(2*c.energy x*(c.energy x^2*R^2)) := by
          calc
            _ = 2*c.energy x*(G x*(c.energy x^2*R^2)) := by rw [prod,mul_one]
            _ = _ := by ring
        _ ≤ _ := mm
    dsimp only [m]
    field_simp [kp.ne',ap.ne',e.ne']
    linarith only [red]
  have gc : ContinuousOn G (Ici T) :=
    Real.continuous_exp.comp_continuousOn ((c.log_energy_continuousOn.mono (fun _ ht=>hT.trans ht)).const_mul (-q))
  have derivG (x:ℝ) (hx:T<x) : HasDerivAt G (G x*(q*c.dissipation x/c.energy x)) x := by
    have xt:=hT.trans_lt hx
    have hlog:=((c.energy_hasDerivAt_normal hf xt).log (c.energy_pos xt.le).ne')
    convert (hlog.const_mul (-q)).exp using 1
    dsimp [G]
    ring
  have mono : MonotoneOn (fun x=>G x-m*x) (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (gc.sub (continuousOn_const.mul continuousOn_id))
    · rw [interior_Ici]
      intro x hx
      exact ((derivG x hx).sub ((hasDerivAt_id x).const_mul m)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have hd : HasDerivAt (fun y=>G y-m*y) (G x*(q*c.dissipation x/c.energy x)-m*1) x := (derivG x hx).sub ((hasDerivAt_id x).const_mul m)
      change 0≤deriv (fun y=>G y-m*y) x
      rw [hd.deriv,mul_one]
      exact sub_nonneg.mpr (slope x hx)
  let H := max ((1+T)/G T) (1/m)
  have h1: (1+T)≤H*G T := (div_le_iff₀ (gp T)).mp (le_max_left _ _)
  have h2 : 1≤H*m := (div_le_iff₀ mp).mp (le_max_right _ _)
  have hp : 0<H := (div_pos zero_lt_one mp).trans_le (le_max_right _ _)
  refine ⟨H^(1/q:ℝ),Real.rpow_pos_of_pos hp _,fun t ht=>?_⟩
  have dr:=mono (Set.mem_Ici.mpr (le_refl T)) (Set.mem_Ici.mpr ht) ht
  have time : 1+t≤H*G t := by
    nlinarith only [mul_le_mul_of_nonneg_left dr hp.le,h1,
      mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr ht)]
  have tp : 0<1+t := by linarith
  have lg := Real.log_le_log tp time
  rw [Real.log_mul hp.ne' (gp t).ne'] at lg
  simp only [G,Real.log_exp] at lg
  have ep:=c.energy_pos (hT.trans ht)
  rw [←Real.exp_log ep,Real.rpow_def_of_pos hp,Real.rpow_def_of_pos tp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  change Real.log (c.energy t)≤Real.log H*(1/q)+Real.log (1+t)*(-(1/q))
  field_simp [qp.ne']
  linarith only [lg]

theorem power_rates_of_stress_fraction (hf : c.IsNormalFEF) {T K : ℝ}
    (hT : 0≤T) (hK : 1≤K)
    (h : ∀t>T, Real.sqrt (c.normalizedProduct t)≤K*c.stressScale t) :
    (∃ C : ℝ,0<C ∧ ∀t≥T,c.length t≤C*(1+t)^(K/(2*K+2))) ∧
    (∃ C : ℝ,0<C ∧ ∀t≥T,c.energy t≤C*(1+t)^(-(1/(2*K+2)))) := by
  obtain ⟨B,cap⟩:=c.length_log_cap hf hT hK h
  exact ⟨c.length_rate_of_cap hf hT hK cap,c.energy_rate_of_cap hf hT hK h cap⟩

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.power_rates_of_stress_fraction
