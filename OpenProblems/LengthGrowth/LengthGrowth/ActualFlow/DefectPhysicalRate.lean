import LengthGrowth.ActualFlow.DefectNormalizedRate
import LengthGrowth.ActualFlow.ForwardRescaling

noncomputable section
open MeasureTheory
namespace LengthGrowth.ClosedFrenetCurve
variable (c : ClosedFrenetCurve)

theorem normalized_bending_quadratic (len : c.period=2*Real.pi)
    (above : 4*Real.pi^2<2*c.energy*c.period) (cap : 2*c.energy*c.period≤4*Real.pi^2+36) :
    (2*c.energy-c.period)^2/1000000 ≤
      c.period*c.dissipation-c.energy*(∫ s in 0..c.period,c.curvature s*c.force s) := by
  rcases c.low_product_turning cap with pos|neg
  · exact c.normalized_positive_turn_quadratic len (pos.trans len.symm) above cap
  · have turn : (∫ s in 0..c.bendingReflection.period,c.bendingReflection.curvature s)=c.bendingReflection.period := by
      change (∫ s in 0..c.period,-c.curvature s)=c.period
      rw [intervalIntegral.integral_neg,neg,neg_neg,len]
    have h := c.bendingReflection.normalized_positive_turn_quadratic len turn
      (by rwa [c.bending_reflection_energy]) (by rwa [c.bending_reflection_energy])
    rw [c.bending_reflection_energy,c.bending_reflection_dissipation] at h
    simp only [c.bending_reflection_force] at h
    change (2*c.energy-c.period)^2/1000000 ≤
      c.period*c.dissipation-c.energy*(∫ s in 0..c.period,(-c.curvature s)*(-c.force s)) at h
    simpa only [neg_mul_neg] using h

end LengthGrowth.ClosedFrenetCurve

namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- A quantitative reverse estimate for the true dissipation gap on every
physical slice of positive defect at most 36, in arbitrary length units. -/
theorem quantitative_bending_gap {s : ℝ} (hs : 0≤s)
    (above : 4*Real.pi^2<2*c.normalizedProduct s) (cap : 2*c.normalizedProduct s≤4*Real.pi^2+36) :
    (4*Real.pi^2/1000000)*(2*c.normalizedProduct s-4*Real.pi^2)^2 ≤
      c.length s^4*(c.length s*c.dissipation s-c.energy s*c.lengthRate s) := by
  let L := c.length s
  let P := 2*Real.pi
  let r := P/L
  have lp : 0<L := c.length_pos hs
  have pp : 0<P := by dsimp [P]; positivity
  have rp : 0<r := div_pos pp lp
  let h := c.rescaled r s rp hs
  let g := h.regularPositionAt (show 0≤(0:ℝ) by rfl)
  let p := g.closedFrenetCurve
  have rL : r*L=P := by dsimp [r]; field_simp
  have hlen : p.period=r*L := by
    change h.length 0=r*c.length s
    simpa only [zero_div,add_zero] using c.rescaled_length r s rp hs 0
  have he : p.energy=c.energy s/r := by
    have aux : p.energy=h.energy 0 := g.closedFrenetCurve_energy
    rw [aux]; exact (c.rescaled_energy r s rp hs 0).trans (by rw [zero_div,add_zero])
  have hd : p.dissipation=c.dissipation s/r^5 := by
    have aux : p.dissipation=h.dissipation 0 := g.closedFrenetCurve_dissipation
    rw [aux]; exact (c.rescaled_dissipation r s rp hs 0).trans (by rw [zero_div,add_zero])
  have hj : (∫ x in 0..p.period,p.curvature x*p.force x)=c.lengthRate s/r^3 := by
    have aux : (∫ x in 0..p.period,p.curvature x*p.force x)=h.lengthRate 0 := g.arclength_integral_curvature_force
    rw [aux]; exact (c.rescaled_lengthRate r s rp hs 0).trans (by rw [zero_div,add_zero])
  have prod : 2*p.energy*p.period=2*c.normalizedProduct s := by
    rw [he,hlen]; change 2*(c.energy s/r)*(r*L)=2*(c.energy s*L); field_simp
  have raw := p.normalized_bending_quadratic (hlen.trans rL) (prod ▸ above) (prod ▸ cap)
  rw [hj,hd,he,hlen] at raw
  have p2 : P^2=4*Real.pi^2 := by dsimp only [P]; ring
  rw [←p2]
  change (P^2/1000000)*(2*(c.energy s*L)-P^2)^2≤L^4*(L*c.dissipation s-c.energy s*c.lengthRate s)
  dsimp only [r] at raw
  field_simp [lp.ne',pp.ne'] at raw
  linarith only [raw]

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.quantitative_bending_gap
