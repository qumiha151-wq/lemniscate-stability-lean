import LengthGrowth.ActualFlow.EnclosingDisk
import LengthGrowth.ActualFlow.RadiusGrowthTime

noncomputable section
namespace LengthGrowth.ActualFlow.ForwardImmersion
variable (c : ForwardImmersion)

/-- The enclosing radius of the actual image on each forward slice. -/
def circumradius (t : ℝ) : ℝ :=
  if ht : 0≤t then (c.regularPositionAt ht).closedFrenetCurve.circumradius else 0

theorem circumradius_slice_controls {t : ℝ} (ht : 0≤t) :
    c.energy t ≤ 2*c.dissipation t*(c.circumradius t)^4 ∧
    1 ≤ c.energy t*c.circumradius t := by
  let p:=c.regularPositionAt ht
  have he : p.closedFrenetCurve.energy=c.energy t := p.closedFrenetCurve_energy
  have hd : p.closedFrenetCurve.dissipation=c.dissipation t := p.closedFrenetCurve_dissipation
  simpa only [circumradius,dif_pos ht,he,hd,p] using p.closedFrenetCurve.circumradius_controls

/-- The sharp unconditional limsup lower bound, expressed without boundedness
of the radius-to-time quotient. Every coefficient below two is exceeded
at an arbitrarily late time. -/
theorem arbitrarily_late_circumradius_exceeds (hf : c.IsNormalFEF) {C : ℝ}
    (hC : 0<C) (small : C<2) (T : ℝ) :
    ∃t, 0<t ∧ T<t ∧ C*t<(c.circumradius t)^4 :=
  c.large_radius_time_of_slice_bounds hf hC small T c.circumradius
    (fun _ ht => c.circumradius_slice_controls ht.le)

end LengthGrowth.ActualFlow.ForwardImmersion
#print axioms LengthGrowth.ActualFlow.ForwardImmersion.arbitrarily_late_circumradius_exceeds
