import LengthGrowth.ActualFlow.TurningQuarterFlow
import LengthGrowth.ActualFlow.TangentModulus

noncomputable section
open Set
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A failure of the exact fourth-root upper estimate forces, at
arbitrarily late high product records, a fixed angular oscillation on
a short interval in every increasing one-period coordinate. -/
theorem no_tangent_modulus_at_high_records (hf : c.IsNormalFEF)
    (fail : ¬c.HasQuarterLengthBound) {η : ℝ} (hp : 0<η) (T M : ℝ) :
    ∃ t,∃ ht : 0<t,T<t ∧ M<c.normalizedProduct t ∧
      (∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
      ¬(c.regularPositionAt ht.le).HasQuarterTurnModulus η := by
  let a := (16/(2^23):ℝ)^(1/6:ℝ)
  have ap : 0<a := by dsimp [a]; positivity
  let w := (1/η)/a+1
  have wp : 0<w := by dsimp [w]; positivity
  obtain ⟨t,ht,late,high,record,m,realized,lower⟩ :=
    c.turning_excursions_at_high_records hf fail T (max M (w^3))
  refine ⟨t,ht,late,lt_of_le_of_lt (le_max_left ..) high,record,?_⟩
  intro mod
  have upper:=(c.regularPositionAt ht.le).turning_count_of_modulus hp mod realized
  have cubelt:=lt_of_le_of_lt (le_max_right ..) high
  have rootlt:=Real.rpow_lt_rpow (by positivity : 0≤w^3) cubelt (by norm_num : (0:ℝ)<1/3)
  rw [←Real.rpow_natCast w 3,←Real.rpow_mul wp.le] at rootlt
  norm_num at rootlt
  have hlt : (1/η)/a < c.normalizedProduct t^(1/3:ℝ) := by
    dsimp [w] at rootlt
    linarith
  have strict := (div_lt_iff₀ ap).mp hlt
  change a*c.normalizedProduct t^(1/3:ℝ)≤(m:ℝ) at lower
  nlinarith only [strict,upper,lower]

/-- A common late-time tangent modulus at the single chord threshold
sin(1/4) implies the exact fourth-root upper bound. The increasing
normalized period coordinate is allowed to vary with the slice. -/
theorem quarter_length_of_tangent_modulus (hf : c.IsNormalFEF) {T M η : ℝ} (hp : 0<η)
    (modu : ∀t,(ht:0<t) → T<t → M<c.normalizedProduct t →
      (c.regularPositionAt ht.le).HasQuarterTurnModulus η) : c.HasQuarterLengthBound := by
  by_contra fail
  obtain ⟨t,ht,late,high,_,bad⟩:=c.no_tangent_modulus_at_high_records hf fail hp T M
  exact bad (modu t ht late high)

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.no_tangent_modulus_at_high_records
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_tangent_modulus
