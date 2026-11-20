import LengthGrowth.ActualFlow.MacroscopicTurningRecords
import LengthGrowth.ActualFlow.TurningMaterial

noncomputable section
open Set Filter FreeElasticScalar
open scoped Topology
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- Failure of the exact quarter-power upper estimate forces many
disjoint quarter-radian net turns at late records on the same flow. -/
theorem turning_excursions_at_high_records (hf : c.IsNormalFEF) (fail : ¬ c.HasQuarterLengthBound)
    (T M : ℝ) :
    ∃t, ∃ht : 0<t, T<t ∧ M<c.normalizedProduct t ∧
      (∀s∈Icc 0 t,c.normalizedProduct s≤c.normalizedProduct t) ∧
      ∃m : ℕ,(c.regularPositionAt ht.le).HasTurningExcursions m ∧
        (16/(2^23):ℝ)^(1/6:ℝ)*c.normalizedProduct t^(1/3:ℝ)≤(m:ℝ) := by
  apply c.macroscopic_witness_at_high_records hf fail (by positivity : 0<(2^23:ℝ)) _ T M
  intro t ht d low
  let p:=c.regularPositionAt ht.le
  obtain ⟨m,realized,estimate⟩:=p.has_turning_excursions_of_low_dissipation low
  refine ⟨m,realized,?_⟩
  change 4*(c.normalizedProduct t)^2≤(2^23:ℝ)*(m:ℝ)^6*d at estimate
  nlinarith only [estimate]

/-- When the realizable counts on late high-product slices lie below
the explicit cube-root threshold, the sharp fourth-root bound follows
for the actual evolving length. -/
theorem quarter_length_of_turning_excursion_bound (hf : c.IsNormalFEF) {T M : ℝ}
    (small : ∀t,(ht:0<t) → T<t → M<c.normalizedProduct t → ∀m : ℕ,
      (c.regularPositionAt ht.le).HasTurningExcursions m →
      (m:ℝ)<(16/(2^23):ℝ)^(1/6:ℝ)*c.normalizedProduct t^(1/3:ℝ)) : c.HasQuarterLengthBound := by
  by_contra fail
  obtain ⟨t,ht,hT,hi,_,m,realized,bound⟩:=c.turning_excursions_at_high_records hf fail T M
  exact (not_lt_of_ge bound) (small t ht hT hi m realized)

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.turning_excursions_at_high_records
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_turning_excursion_bound
