import LengthGrowth.ActualFlow.CriticalDensityTime

/-! The critical count grows like the cube root of the scale-invariant
energy-length product. A smaller power gives a quantitative log correction. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

theorem count_deficit_to_power {U z n B C σ : ℝ} (hu : 0<U) (hn : 0≤n)
    (hB : 0≤B) (hC : 0≤C) (count : n≤B*U^σ)
    (deficit : Real.sqrt U ≤ z+C*n*Real.sqrt n) :
    U^((1-3*σ)/2)*(Real.sqrt U-z) ≤ C*B^(3/2:ℝ)*Real.sqrt U := by
  have pw:=Real.rpow_le_rpow hn count (by norm_num : (0:ℝ)≤3/2)
  have eqn : n^(3/2:ℝ)=n*Real.sqrt n := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add_of_nonneg hn (by norm_num) (by norm_num),
      Real.rpow_one,←Real.sqrt_eq_rpow]
  rw [eqn,Real.mul_rpow hB (Real.rpow_nonneg hu.le σ),←Real.rpow_mul hu.le] at pw
  have diff : Real.sqrt U-z ≤ C*B^(3/2:ℝ)*U^(σ*(3/2:ℝ)) := by
    nlinarith only [deficit,mul_le_mul_of_nonneg_left pw hC]
  calc
    _ ≤ U^((1-3*σ)/2)*(C*B^(3/2:ℝ)*U^(σ*(3/2:ℝ))) :=
      mul_le_mul_of_nonneg_left diff (Real.rpow_nonneg hu.le _)
    _ = C*B^(3/2:ℝ)*(U^((1-3*σ)/2)*U^(σ*(3/2:ℝ))) := by ring
    _ = _ := by rw [←Real.rpow_add hu,show (1-3*σ)/2+σ*(3/2:ℝ)=1/2 by ring,←Real.sqrt_eq_rpow]

theorem length_energy_of_subcritical_count (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T B C σ U₀ : ℝ} (hT : 0≤T) (hB : 0≤B) (hC : 0≤C) (hσ : σ<1/3)
    (slices : ∀t>T,U₀≤c.normalizedProduct t → ∃ n : ℝ, 0≤n ∧ n≤B*c.normalizedProduct t^σ ∧
      Real.sqrt (c.normalizedProduct t)≤c.stressScale t+C*n*Real.sqrt n) :
    (∃ H : ℝ, 0<H ∧ ∀t≥T,c.length t≤H*fourthRoot (1+t)*(1+Real.log (1+t))^(1/(1-3*σ))) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  have hq : 0<(1-3*σ)/2 := by linarith
  have result:=c.length_energy_of_power_deficit hf (U₀:=U₀) hT hq
    (mul_nonneg hC (Real.rpow_nonneg hB (3/2:ℝ))) (fun t ht hU => by
      obtain ⟨n,hn,cap,deficit⟩:=slices t ht hU
      exact count_deficit_to_power (mul_pos (c.energy_pos (hT.trans ht.le)) (c.length_pos (hT.trans ht.le)))
        hn hB hC cap deficit)
  simpa only [show 2*((1-3*σ)/2)=1-3*σ by ring] using result

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.length_energy_of_subcritical_count
