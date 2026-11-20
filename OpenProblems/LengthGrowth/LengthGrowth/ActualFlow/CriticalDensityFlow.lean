import LengthGrowth.ActualFlow.CriticalDensityCountRate
import LengthGrowth.ActualFlow.CriticalDensityMaterial

/-! Bounds for a single actual flow. Small reversals of signed curvature
are allowed arbitrarily often inside each half-RMS piece. -/
noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
set_option backward.isDefEq.respectTransparency false
namespace LengthGrowth.ActualFlow.ForwardImmersion

theorem log_power_length_of_half_rms_pieces (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T B σ U₀ : ℝ} (hT : 0≤T) (hB : 0≤B) (hσ : σ<1/3)
    (pieces : ∀t,(ht:T<t) → U₀≤c.normalizedProduct t → ∃ N : ℕ,
      (c.regularPositionAt (hT.trans ht.le)).CriticalDensityCount N ∧
      (N:ℝ)+1≤B*c.normalizedProduct t^σ) :
    (∃ H : ℝ, 0<H ∧ ∀t≥T,c.length t≤H*fourthRoot (1+t)*(1+Real.log (1+t))^(1/(1-3*σ))) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  apply c.length_energy_of_subcritical_count hf (U₀:=U₀) hT hB (show (0:ℝ)≤2048 by norm_num) hσ
  intro t ht hu
  obtain ⟨N,hN,bound⟩:=pieces t ht hu
  exact ⟨(N:ℝ)+1,by positivity,bound,(c.regularPositionAt (hT.trans ht.le)).criticalDensity_dissipation_bound N hN⟩

/-- The number of true inflections may be infinite. A uniform count
of alternating excursions beyond half the RMS already suffices. -/
theorem log_quarter_of_bounded_half_rms_pieces (c : ForwardImmersion) (hf : c.IsNormalFEF)
    {T : ℝ} (hT : 0≤T) (N : ℕ)
    (pieces : ∀t,(ht:T<t) → (c.regularPositionAt (hT.trans ht.le)).CriticalDensityCount N) :
    (∃ H : ℝ, 0<H ∧ ∀t≥T,c.length t≤H*fourthRoot (1+t)*(1+Real.log (1+t))) ∧
      Tendsto c.energy atTop (𝓝 0) := by
  have main:=c.log_power_length_of_half_rms_pieces hf (U₀:=0) hT
    (show 0≤(N:ℝ)+1 by positivity) (show (0:ℝ)<1/3 by norm_num)
    (fun t ht _ => ⟨N,pieces t ht,by simp⟩)
  simpa using main

end LengthGrowth.ActualFlow.ForwardImmersion

#print axioms LengthGrowth.ActualFlow.ForwardImmersion.log_power_length_of_half_rms_pieces
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.log_quarter_of_bounded_half_rms_pieces
