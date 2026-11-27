import LengthGrowth.ActualFlow.IntegrableInflectionGrowth
import LengthGrowth.ActualFlow.PhysicalInflectionRate
import LengthGrowth.ActualFlow.ContinuousInflectionMajorant

noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.ForwardImmersion

/-- Integrability of the actual largest outward inflection speed on a
    single tail gives fourth-root length growth for that closed curve. -/
theorem quarter_length_of_integrable_physical_inflection_rate (c : ForwardImmersion)
    (flow : c.IsNormalFEF) {T : ℝ} (tp : 0<T)
    (finite : IntegrableOn c.physicalInflectionRate (Ioi T)) : c.HasQuarterLengthBound := by
  obtain ⟨r,cr,ir,pos,dominates⟩ := TurningEnvelope.exists_continuous_integrable_tail_majorant
    (c.physicalInflectionRate_upperSemicontinuousOn.mono (Ioi_subset_Ioi tp.le))
    (fun t ht=>c.physicalInflectionRate_nonneg (tp.trans ht)) finite
  apply c.quarter_length_of_integrable_outward_inflection_bound flow r cr ir (fun t _=>pos t)
  intro t ht x y kx gx ky gy
  exact (c.le_physicalInflectionRate (show 0<t by linarith) x y kx gx ky gy).trans (dominates t ht)

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_integrable_physical_inflection_rate
