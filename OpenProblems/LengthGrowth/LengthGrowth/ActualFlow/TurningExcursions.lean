import LengthGrowth.ActualFlow.TurningSlice
import LengthGrowth.ActualFlow.TurningFamily

noncomputable section
open Set Function MeasureTheory FreeElasticScalar
open scoped ContDiff
namespace LengthGrowth.ActualFlow.PeriodicRegularPosition

/-- A single period, beginning at any arclength origin, contains m arcs
with disjoint interiors, each enclosing at least one quarter radian of
absolute net tangent rotation. RMS scaling preserves each signed angle. -/
def HasTurningExcursions (p : PeriodicRegularPosition) (m : ℕ) : Prop :=
  let P := Real.sqrt (2*(materialEnergy p.position p.period*p.length))
  ∃ a : ℝ, MacroscopicTurning.ExcursionFamily
    (p.scaledArclengthCurvature (p.length/P)) a (a+P) m

theorem turning_excursions_transfer (p : PeriodicRegularPosition)
    (pack : ∀ {k : ℝ→ℝ} {P M : ℝ}, 0<P → ContDiff ℝ ∞ k → Periodic k P →
      (∫x in 0..P,k x^2)=P → (∫x in 0..P,|FiniteSignWindow.force k x|)≤P/2 →
      (∀x,|k x|≤M) → 1/4≤∫x in 0..P,|k x| →
      ∃ a m, MacroscopicTurning.ExcursionFamily k a (a+P) m ∧ P≤(m:ℝ)*M)
    (low : 4*(materialDissipation p.position p.period*p.length^2 /
      (8*(materialEnergy p.position p.period)^3))≤1) :
    ∃m : ℕ, p.HasTurningExcursions m ∧
      4*(materialEnergy p.position p.period*p.length)^2 ≤ (2^23:ℝ)*(m:ℝ)^6*
        (materialDissipation p.position p.period*p.length^2/(8*(materialEnergy p.position p.period)^3)) := by
  let E:=materialEnergy p.position p.period
  let L:=p.length
  let P:=Real.sqrt (2*(E*L))
  let h:=L/P
  let u:=p.scaledArclengthCurvature h
  let d:=materialDissipation p.position p.period*L^2/(8*E^3)
  obtain ⟨hP,ku,per,rms,charge,M,hm,cap,power⟩:=p.turning_slice_bounds low
  change 0<P at hP
  change M^6≤(2^23:ℝ)*P^2*d at power
  have total : 1/4≤∫s in 0..P,|u s| := by
    have span : h*P=p.length := div_mul_cancel₀ _ hP.ne'
    have a0 : 0<h := div_pos p.length_pos hP
    rw [show (∫s in 0..P,|u s|)=p.closedFrenetCurve.absoluteCurvature from
      p.scaled_total_absolute_turn a0 span]
    exact (by norm_num : (1/4:ℝ)≤1).trans p.closedFrenetCurve.one_le_absoluteCurvature
  obtain ⟨a,m,arcs,width⟩:=pack hP ku per rms charge cap total
  refine ⟨m,⟨a,arcs⟩,?_⟩
  have pair : P^2=2*(E*L) := Real.sq_sqrt (by positivity [p.material_energy_pos,p.length_pos])
  have width6:=pow_le_pow_left₀ hP.le width 6
  rw [mul_pow] at width6
  have joint := width6.trans (mul_le_mul_of_nonneg_left power (show 0≤(m:ℝ)^6 by positivity))
  change 4*(E*L)^2 ≤ (2^23:ℝ)*(m:ℝ)^6*d
  rw [show 4*(E*L)^2=P^4 by nlinarith only [congrArg (fun z:ℝ=>z^2) pair]]
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hP)).mp
  nlinarith only [joint]

end LengthGrowth.ActualFlow.PeriodicRegularPosition
#print axioms LengthGrowth.ActualFlow.PeriodicRegularPosition.turning_excursions_transfer
