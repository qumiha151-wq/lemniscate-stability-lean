import SolitonClassification.PrescribedPhysicalChart
import SolitonClassification.PrescribedImpactSigns
import SolitonClassification.PrescribedSeamPhase
import SolitonClassification.WindingClosesCurves
import SolitonClassification.FrozenKernelEndpoints
import SolitonClassification.SeamFlightClearance

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam

abbrev Curvatures := Icc (-1/4:ℝ) 1
abbrev ChartDomain (E : ℝ) := Curvatures × Icc (0:ℝ) E
def leftCurvature : Curvatures := ⟨-1/4,by constructor <;> norm_num⟩
def rightCurvature : Curvatures := ⟨1,by constructor <;> norm_num⟩

/-- A matched-height seam family at prescribed physical inverse radius. Its
    abstract coordinates extend to radius parameter zero, while all positive
    parameters have actual realizations by coefficient-one seam trajectories. -/
structure WindingChart (H E : ℝ) where
  angle : ChartDomain E → ℝ
  transverse : ChartDomain E → ℝ
  continuous_angle : Continuous angle
  continuous_transverse : Continuous transverse
  bounded : ∃M:ℝ, ∀z, |angle z|≤M
  left : ∀e, transverse (leftCurvature,e)< -0.001
  right : ∀e, 0.5<transverse (rightCurvature,e)
  physical : ∀z : ChartDomain E, 0<(z.2:ℝ) →
    ∃Y : Phase, ∃t<0, Y 1=0 ∧ Y 3=0 ∧
      let y := solution 1 Y t
      regular y ∧ 4≤root y/scale y ∧ 0≤along y ∧
      ReflectedArc.RadialLayer.eps (solution 1 Y) t=z.2 ∧
      height y= -H ∧ sectionImpact y=transverse z ∧ hasAngle y (angle z)

/-- A physical realization whose final arclength is continuous in the data
and vanishes at inverse radius zero. -/
structure WindingChart.Flight {H E : ℝ} (w : WindingChart H E) where
  length : ChartDomain E → ℝ
  continuous_length : Continuous length
  frozen_length : ∀ z : ChartDomain E, (z.2:ℝ)=0 → length z=0
  realizes : ∀ z : ChartDomain E, 0<(z.2:ℝ) →
    ∃ Y : Phase, let t := -length z
      t<0 ∧ Y 1=0 ∧ Y 3=0 ∧
      let y := solution 1 Y t
      regular y ∧ 4≤root y/scale y ∧ 0≤along y ∧
        ReflectedArc.RadialLayer.eps (solution 1 Y) t=z.2 ∧
        height y= -H ∧ sectionImpact y=w.transverse z ∧ hasAngle y (w.angle z)

/-- The certified seam faces, including their actual last arclength. -/
theorem exists_winding_chart_with_flight :
    ∃H₀, ∀H≥H₀, ∃E>0, ∃ v : WindingChart H E, Nonempty v.Flight := by
  obtain ⟨H₀,sect⟩ := prescribed_seam_sections (-1/4) 1
  obtain ⟨B,far⟩ := prescribed_sector_strip (-1/4) 1
  refine ⟨max H₀ B,?_⟩
  intro H hH
  obtain ⟨E,ep,⟨w⟩⟩ := sect H ((le_max_left ..).trans hH)
  have ends (t : ℝ) (ht : 20≤t) := FrozenStress.Endpoint.realized_seams_on_both_tails t
    (ht.trans (le_abs_self t))
  obtain ⟨D,hD,face⟩ := w.impact_strip (by norm_num) ep
    (α:=-0.001) (β:=0.5) (fun t ht => ((ends t ht).1).trans (by norm_num)) (fun t ht => lt_trans (by norm_num) (ends t ht).2)
  obtain ⟨R,hR,sectorBound⟩ := far H ((le_max_right ..).trans hH) E ep w
  obtain ⟨θ,cθ,phase,M,bound⟩ := w.phase_lift (by norm_num) ep.le
  let A := min D R
  have aPos : 0<A := lt_min hD.1 hR.1
  let j := fun e : Icc (0:ℝ) A => (⟨e, e.property.1, e.property.2.trans ((min_le_left ..).trans hD.2)⟩ : Icc (0:ℝ) E)
  let f := fun z : ChartDomain A => (z.1,j z.2)
  have cj : Continuous j := continuous_subtype_val.subtype_mk _
  have cf : Continuous f := continuous_fst.prodMk (cj.comp continuous_snd)
  let time := fun z : ChartDomain A => w.physicalFlight (f z)
  have lift (z : ChartDomain A) (pos : 0<(z.2:ℝ)) :
      ∃ Y : Phase, let t := -time z
        t<0 ∧ Y 1=0 ∧ Y 3=0 ∧
        let y := solution 1 Y t
        regular y ∧ 4≤root y/scale y ∧ 0≤along y ∧
          ReflectedArc.RadialLayer.eps (solution 1 Y) t=z.2 ∧
          height y= -H ∧ sectionImpact y=w.sectionImpact (f z).1 (f z).2 ∧
          hasAngle y (θ (f z)) := by
    let x := w.normalizedState (f z)
    obtain ⟨l,hl,scaleEq,tn,v,q,reg,eps,hh,hit,al,rr,sh,sl⟩ := w.physical_chart (f z) pos
    let Y := restore l ![((f z).1:ℝ),0,1,0]
    let t := -w.flight (f z)/l
    let y := solution 1 Y t
    have et : -(time z)=t := by
      dsimp only [time,t]
      rw [w.physicalFlight_eq hl scaleEq]
      exact (neg_div l (w.flight (f z))).symm
    have se : sector x := sectorBound (f z) (z.2.property.2.trans (min_le_right ..))
    have P : hasAngle x (θ (f z)) := phase (f z)
    refine ⟨Y,?_⟩
    dsimp only
    rw [et]
    refine ⟨tn,v,q,reg,se.2.le.trans_eq rr.symm,se.1.le.trans_eq al.symm,eps,by linarith,hit,?_⟩
    change hasAngle y (θ (f z))
    unfold hasAngle at P ⊢
    change shape y=shape x at sh
    change slope y=slope x at sl
    rwa [sh,sl]
  let v : WindingChart H A :=
    ⟨θ ∘ f,fun z => w.sectionImpact (f z).1 (f z).2,cθ.comp cf,
      w.continuous_impact.comp cf,⟨M,fun z => bound (f z)⟩,
      fun e => (face (j e) (e.property.2.trans (min_le_left ..))).1,
      fun e => (face (j e) (e.property.2.trans (min_le_left ..))).2,fun z hp => by
        obtain ⟨Y,hy⟩ := lift z hp
        exact ⟨Y,-time z,hy⟩⟩
  refine ⟨A,aPos,v,⟨⟨time,w.continuous_physicalFlight.comp cf,?_,lift⟩⟩⟩
  intro z hzero
  have fr := w.frozen (f z) hzero
  simp [time,PrescribedSection.physicalFlight,fr]

/-- All geometry and endpoint inequalities for the seam faces, with no
    shooting, numerical or regularity assumptions. -/
theorem exists_winding_chart : ∃H₀, ∀H≥H₀, ∃E>0, Nonempty (WindingChart H E) := by
  obtain ⟨H₀,h⟩ := exists_winding_chart_with_flight
  refine ⟨H₀,fun H hH => ?_⟩
  obtain ⟨E,hE,w,_⟩ := h H hH
  exact ⟨E,hE,⟨w⟩⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.exists_winding_chart
