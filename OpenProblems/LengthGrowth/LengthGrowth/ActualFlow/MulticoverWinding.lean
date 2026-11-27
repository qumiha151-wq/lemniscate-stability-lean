import LengthGrowth.ActualFlow.MulticoverFlow

noncomputable section
open Set
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A linear-in-m curvature-oscillation sublevel for either orientation.
The input contains only the integer turning and the initial product. -/
theorem multicover_winding_sublevel (hf : c.IsNormalFEF) (m : ℕ) (hm : 1≤m)
    (turn : c.initialAbsoluteTurning=2*Real.pi*(m:ℝ))
    (initial : 2*c.normalizedProduct 0-(2*Real.pi*(m:ℝ))^2≤12*Real.pi*(m:ℝ)/5+9/25) :
    AntitoneOn c.normalizedProduct (Ici 0) ∧ c.HasQuarterLengthBound ∧ c.HasQuarterEnergyBound ∧
    (∀t,0≤t → c.length t≤2*c.length 0 ∨ c.length t^4≤4*(2*c.normalizedProduct 0)^2*t) := by
  have m1 : (1:ℝ)≤(m:ℝ):=by exact_mod_cast hm
  have six : 6≤c.initialAbsoluteTurning:=by rw [turn];nlinarith only [m1,Real.pi_gt_three,mul_nonneg Real.pi_pos.le (sub_nonneg.mpr m1)]
  have cap : c.rootBending 0≤c.initialAbsoluteTurning+3/5:=by
    rw [turn]
    have a:=c.rootBending_sq (le_refl 0)
    have b : 0≤2*Real.pi*(m:ℝ):=by positivity
    nlinarith only [a,b,initial]
  have anti:=c.multicover_product_antitone hf six cap
  have bounded : c.HasBoundedEnergyLength:=⟨c.normalizedProduct 0,fun _ ht=>anti self_mem_Ici ht ht⟩
  have length:=(c.quarter_length_iff_bounded_energyLength hf).mpr bounded
  exact ⟨anti,length,c.quarter_energy_of_quarter_length hf length,fun _ ht=>c.multicover_explicit_length hf six cap ht⟩
end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.multicover_winding_sublevel
