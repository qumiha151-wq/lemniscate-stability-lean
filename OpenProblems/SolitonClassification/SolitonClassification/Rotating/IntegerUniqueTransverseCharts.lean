import SolitonClassification.Rotating.IntegerChartUniqueness
import SolitonClassification.Rotating.IntegerCrossingTransverse

namespace SolitonClassification.Rotating.IntegerTarget.CrossingCharts
noncomputable section
open Set

/-- Each of the two specified rectangles contains exactly one pair of
crossing parameters. The corresponding position intervals are disjoint. -/
theorem unique_transverse_chart {c : Parameters} (hc : c∈cube) (k : Fin 2) :
    ∃! p : ℝ×ℝ, p.1∈dom k false ∧ p.2∈dom k true ∧
      gridPosition c p.1 = gridPosition c p.2 ∧
      1/4 < |Real.sin (gridAngle c p.2-gridAngle c p.1)| := by
  obtain ⟨x,hx,y,hy,e⟩ := chart_intersection hc k
  refine ⟨(x,y),⟨hx,hy,e,crossing_angles_transverse hc hx hy⟩,?_⟩
  rintro ⟨u,v⟩ ⟨hu,hv,e',_⟩
  have indep (s) (hs : s∈dom k false) (t) (ht : t∈dom k true) :
      Real.sin (gridAngle c t-gridAngle c s)≠0 := abs_pos.mp (by linarith [crossing_angles_transverse hc hs ht])
  obtain ⟨rfl,rfl⟩ := unique_chart_parameters hc indep hu hv hx hy e' e
  rfl

end
end SolitonClassification.Rotating.IntegerTarget.CrossingCharts
#print axioms SolitonClassification.Rotating.IntegerTarget.CrossingCharts.unique_transverse_chart

