import LengthGrowth.ActualFlow.DefectReflection
import LengthGrowth.ActualFlow.DefectTurningGap
import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section
open Set Filter Topology MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

theorem bending_sublevel_strict (above : 4*Real.pi^2<2*c.energy*c.period)
    (below : 2*c.energy*c.period≤4*Real.pi^2+36) :
    c.energy*(∫ s in 0..c.period,c.curvature s*c.force s)<c.period*c.dissipation := by
  rcases c.low_product_turning below with pos|neg
  · exact c.bending_one_turn_strict pos above below
  · exact c.bending_negative_turn_strict neg above below

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The derivative of the physical product extends to time zero from the
right using the continuous physical rate. No evolution for negative times
is assumed. -/
theorem normalizedProduct_right_derivative (hf : c.IsNormalFEF) {s : ℝ} (hs : 0≤s) :
    HasDerivWithinAt c.normalizedProduct
      (c.energy s*c.lengthRate s-c.length s*c.dissipation s) (Ici 0) s := by
  rcases eq_or_lt_of_le hs with eq|pos
  · subst s
    apply hasDerivWithinAt_Ici_of_tendsto_deriv (s:=Ioi 0)
    · exact fun x hx => (c.normalizedProduct_hasDerivAt_normal hf hx).differentiableAt.differentiableWithinAt
    · exact (c.normalizedProduct_continuousOn 0 self_mem_Ici).mono Ioi_subset_Ici_self
    · exact self_mem_nhdsWithin
    · have hc := (c.energy_continuousOn.mul c.lengthRate_continuousOn).sub
        (c.length_continuousOn.mul c.dissipation_continuousOn)
      have cont := (hc 0 self_mem_Ici).mono Ioi_subset_Ici_self
      apply cont.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (c.normalizedProduct_hasDerivAt_normal hf hx).deriv.symm
  · exact (c.normalizedProduct_hasDerivAt_normal hf pos).hasDerivWithinAt

theorem bending_rate_strict {s : ℝ} (hs : 0≤s)
    (above : 4*Real.pi^2<2*c.normalizedProduct s)
    (below : 2*c.normalizedProduct s≤4*Real.pi^2+36) :
    c.energy s*c.lengthRate s<c.length s*c.dissipation s := by
  let g := c.regularPositionAt hs
  let p := g.closedFrenetCurve
  have e : p.energy=c.energy s := g.closedFrenetCurve_energy
  have d : p.dissipation=c.dissipation s := g.closedFrenetCurve_dissipation
  have l : p.period=c.length s := rfl
  have j : (∫ x in 0..p.period,p.curvature x*p.force x)=c.lengthRate s :=
    g.arclength_integral_curvature_force
  have U : 2*p.energy*p.period=2*c.normalizedProduct s := by
    rw [e,l,normalizedProduct]; ring
  have h := p.bending_sublevel_strict (U ▸ above) (U ▸ below)
  rwa [e,j,l,d] at h

/-- A sufficient condition on the initial geometry of a single physical
forward elastic flow, including the equality endpoint. -/
theorem quarter_length_of_initial_bending_sublevel (hf : c.IsNormalFEF)
    (initial : 2*c.normalizedProduct 0≤4*Real.pi^2+36) : c.HasQuarterLengthBound := by
  apply c.quarter_length_of_bending_sublevel_boundary hf initial
  intro s hs eq
  have strict := c.bending_rate_strict hs (by linarith only [eq]) eq.le
  refine ⟨2*(c.energy s*c.lengthRate s-c.length s*c.dissipation s),by linarith,?_⟩
  exact (c.normalizedProduct_right_derivative hf hs).const_mul 2

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quarter_length_of_initial_bending_sublevel
