import LengthGrowth.ActualFlow.CriticalEndpointTime
import LengthGrowth.ActualFlow.CriticalDensityIndex
import LengthGrowth.ActualFlow.CriticalLowDissipationMaterial

/-! Rates on one geometric flow at the critical cube-root count. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Every high-count slice satisfies an explicit inverse stress bound.
The coefficient B may be a different number on each slice. -/
theorem stress_fraction_of_half_rms_count {t B : ℝ} (ht : 0≤t) (hB : 0≤B)
    (N : ℕ) (cnt : (c.regularPositionAt ht).CriticalDensityCount N)
    (bound : (N:ℝ)+1≤B*(c.normalizedProduct t)^(1/3:ℝ)) :
    Real.sqrt (c.normalizedProduct t)≤(max 2 ((10^8:ℝ)*B^3))*c.stressScale t := by
  let E:=c.energy t
  let L:=c.length t
  let U:=c.normalizedProduct t
  let d:=c.dissipation t*L^2/(8*E^3)
  let K:=max 2 ((10^8:ℝ)*B^3)
  have ep : 0<E := c.energy_pos ht
  have lp : 0<L := c.length_pos ht
  have dp : 0≤d := by dsimp [d]; positivity [c.dissipation_nonneg t]
  have up : 0<U := mul_pos ep lp
  have kp : 2≤K := le_max_left .. 
  have kp0 : 0≤K := by linarith
  have ratio : 1≤4*K^2*d := by
    by_cases low : 16*d≤1
    · have off := (c.regularPositionAt ht).critical_low_dissipation N cnt low
      change (2*U)^2≤(10^16:ℝ)*((N:ℝ)+1)^6*d at off
      have count:=pow_le_pow_left₀ (show 0≤(N:ℝ)+1 by positivity) bound 6
      change ((N:ℝ)+1)^6≤(B*U^(1/3:ℝ))^6 at count
      rw [mul_pow,←Real.rpow_natCast (U^(1/3:ℝ)) 6,←Real.rpow_mul up.le] at count
      norm_num at count
      have cb : (2*U)^2≤(10^16:ℝ)*(B^6*U^2)*d := by
        exact off.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left count (by positivity)) dp)
      have scale : 4≤(10^16:ℝ)*B^6*d := by
        apply (mul_le_mul_iff_left₀ (sq_pos_of_pos up)).mp
        nlinarith only [cb]
      have ksq:=pow_le_pow_left₀ (show 0≤(10^8:ℝ)*B^3 by positivity)
        (show (10^8:ℝ)*B^3≤K from le_max_right ..) 2
      nlinarith only [scale,mul_le_mul_of_nonneg_right ksq dp]
    · have ksq:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) kp 2
      nlinarith only [lt_of_not_ge low,mul_le_mul_of_nonneg_right ksq dp]
  have zz : c.stressScale t ^ 2 = 4*U*d := by
    change (Real.sqrt (c.dissipation t*L^3/(2*E^2)))^2=4*(E*L)*d
    rw [Real.sq_sqrt (by positivity [c.dissipation_nonneg t])]
    dsimp only [d]
    field_simp [ep.ne']
    ring
  change Real.sqrt U ≤ K*c.stressScale t
  apply le_of_not_gt
  intro bad
  have sq:=pow_lt_pow_left₀ bad (mul_nonneg kp0 (Real.sqrt_nonneg _)) (by decide : 2≠0)
  rw [mul_pow,zz,Real.sq_sqrt up.le] at sq
  nlinarith only [sq,mul_le_mul_of_nonneg_left ratio up.le]

/-- A fixed constant times the cube-root reversal scale gives energy
decay by a positive power and a length exponent strictly below one half. -/
theorem power_rates_of_critical_half_rms_index (hf : c.IsNormalFEF) {T U₀ B : ℝ}
    (hT : 0≤T) (hB : 0≤B)
    (count : ∀t,(ht:T<t) → U₀≤c.normalizedProduct t →
      ((c.regularPositionAt (hT.trans ht.le)).criticalDensityIndex:ℝ)+1≤
        B*c.normalizedProduct t^(1/3:ℝ)) :
    ∃ K : ℝ, 1≤K ∧ K/(2*K+2)<1/2 ∧
      (∃ C : ℝ,0<C ∧ ∀t≥T,c.length t≤C*(1+t)^(K/(2*K+2))) ∧
      (∃ C : ℝ,0<C ∧ ∀t≥T,c.energy t≤C*(1+t)^(-(1/(2*K+2)))) := by
  let K:=max (max 2 ((10^8:ℝ)*B^3)) (Real.sqrt U₀)
  have k1 : 1≤K := (by norm_num : (1:ℝ)≤2).trans ((le_max_left ..).trans (le_max_left ..))
  refine ⟨K,k1,?_,c.power_rates_of_stress_fraction hf hT k1 ?_⟩
  · rw [div_lt_iff₀ (by linarith : 0<2*K+2)]
    linarith
  · intro t ht
    have t0:=hT.trans ht.le
    have z : 1≤c.stressScale t := (c.density_stress_control t0).1
    by_cases hi : U₀≤c.normalizedProduct t
    · let p:=c.regularPositionAt t0
      exact (c.stress_fraction_of_half_rms_count t0 hB p.criticalDensityIndex
        p.criticalDensityIndex_spec (count t ht hi)).trans
        (mul_le_mul_of_nonneg_right (le_max_left ..) (zero_le_one.trans z))
    · have small:=Real.sqrt_le_sqrt (le_of_not_ge hi)
      have ks:Real.sqrt U₀≤K:=le_max_right ..
      exact (small.trans ks).trans (by nlinarith only [mul_nonneg (zero_le_one.trans k1) (sub_nonneg.mpr z)])

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.power_rates_of_critical_half_rms_index
