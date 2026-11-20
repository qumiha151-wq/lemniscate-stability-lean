import SolitonClassification.PrescribedSeamSections
import SolitonClassification.SeamPhaseLift

noncomputable section
open Set
namespace ClosedSimilarity.GlobalSupport.MovingSeam

theorem oscillator {z : Phase} (h : regular z) :
    (shape z^2/2)^2+slope z^2=1 := by
  have ap : 0<amplitude z := Real.sqrt_pos.mpr h.2
  have r2 : root z^2=amplitude z := Real.sq_sqrt ap.le
  have a2 : amplitude z^2=(z 0^2/2)^2+z 1^2 := Real.sq_sqrt h.2.le
  unfold shape slope
  rw [show (z 0/root z)^2=z 0^2/amplitude z by rw [div_pow,r2]]
  field_simp [ap.ne']
  nlinarith only [a2]

/-- A single bounded real phase is valid on the entire rectangle of prescribed
    radii, including the frozen boundary and both endpoint curvatures. -/
theorem PrescribedSection.phase_lift {a b H E : ℝ} (w : PrescribedSection a b H E)
    (hab : a≤b) (ep : 0≤E) :
    let F := fun z : Icc a b × Icc (0:ℝ) E => shot (w.drive z) z.1 (-w.flight z)
    ∃ θ : Icc a b × Icc (0:ℝ) E → ℝ, Continuous θ ∧
      (∀z, Real.sin (θ z)=shape (F z)/Real.sqrt 2 ∧
        Real.cos (θ z)=slope (F z)/Real.sqrt (1+shape (F z)^2/2)) ∧ ∃M,∀z,|θ z|≤M := by
  dsimp only
  let X := Icc a b × Icc (0:ℝ) E
  let F := fun z : X => shot (w.drive z) z.1 (-w.flight z)
  have cf : Continuous F := continuous_shot w.continuous_drive (continuous_subtype_val.comp continuous_fst)
    w.continuous_flight.neg
  have cA : Continuous (fun z => amplitude (F z)) := by unfold amplitude stressSquared; fun_prop
  have cR : Continuous (fun z => root (F z)) := cA.sqrt
  have aPos (z : X) : 0<amplitude (F z) := Real.sqrt_pos.mpr (w.regular_incoming z).2
  have cU : Continuous (fun z => shape (F z)) := ((continuous_apply 0).comp cf).div cR
    (fun z => (Real.sqrt_pos.mpr (aPos z)).ne')
  have cw : Continuous (fun z => slope (F z)) := ((continuous_apply 1).comp cf).div cA
    (fun z => (aPos z).ne')
  exact FrozenStress.Incoming.oscillator_angle_lift hab ep _ _ cU cw (fun z => oscillator (w.regular_incoming z))

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.PrescribedSection.phase_lift
