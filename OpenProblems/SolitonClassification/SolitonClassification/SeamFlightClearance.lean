import SolitonClassification.PrescribedPhysicalChart
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Physical arclength of the last flight from a prescribed section to
the reflection seam. The section time is bounded in rescaled units, and
the corresponding arclength tends to zero uniformly over seam curvature. -/
noncomputable section
namespace ClosedSimilarity.GlobalSupport.MovingSeam.PrescribedSection
open Set
variable {a b H E : ℝ} (w : PrescribedSection a b H E)

def physicalFlight (z : Icc a b × Icc (0:ℝ) E) : ℝ :=
  w.flight z * Real.sqrt (Real.sqrt (w.drive z))

theorem continuous_physicalFlight : Continuous w.physicalFlight :=
  w.continuous_flight.mul w.continuous_drive.sqrt.sqrt

theorem physicalFlight_eq {z : Icc a b × Icc (0:ℝ) E} {l : ℝ}
    (hl : 0<l) (scaleEq : l^4*w.drive z=1) : w.physicalFlight z=w.flight z/l := by
  have eq : w.drive z = (l⁻¹^2)^2 := by
    apply (mul_left_cancel₀ (pow_ne_zero 4 hl.ne'))
    rw [scaleEq]
    field_simp
  unfold physicalFlight
  rw [eq,Real.sqrt_sq (sq_nonneg _),Real.sqrt_sq (inv_pos.mpr hl).le,div_eq_mul_inv]

theorem physicalFlight_vanishes_uniformly (hE : 0≤E) (η : ℝ) (hη : 0<η) :
    ∃ e>0, ∀ z : Icc a b × Icc (0:ℝ) E, (z.2:ℝ)<e →
      |w.physicalFlight z|<η := by
  have uc := CompactSpace.uniformContinuous_of_continuous w.continuous_physicalFlight
  obtain ⟨e,he,close⟩ := Metric.uniformContinuous_iff.mp uc η hη
  refine ⟨e,he,?_⟩
  intro z small
  let z₀ : Icc a b × Icc (0:ℝ) E := (z.1,⟨0,le_rfl,hE⟩)
  have zero : w.physicalFlight z₀=0 := by
    simp [physicalFlight,w.frozen z₀ rfl]
  have near : dist z z₀<e := by
    rw [Prod.dist_eq,max_lt_iff]
    refine ⟨by simpa [z₀] using he,?_⟩
    change dist (z.2:ℝ) (0:ℝ)<e
    simpa [Real.dist_eq,abs_of_nonneg z.2.property.1] using small
  have h := close near
  rwa [Real.dist_eq,zero,sub_zero] at h

/-- The actual seam-normalized trajectory traverses less than η physical
arclength, and its radius varies by less than η at every intermediate point. -/
theorem uniform_short_physical_arc (hE : 0≤E) (η : ℝ) (hη : 0<η) :
    ∃ e>0, ∀ z : Icc a b × Icc (0:ℝ) E, (z.2:ℝ)<e →
      ∀ l>0, l^4*w.drive z=1 →
        let Y := restore l ![(z.1:ℝ),0,1,0]
        0<w.flight z/l ∧ w.flight z/l<η ∧
        ∀ s∈Icc (-w.flight z/l) 0,
          |Real.sqrt (radiusSq (solution 1 Y s)) - Real.sqrt (radiusSq Y)|<η := by
  obtain ⟨e,he,small⟩ := w.physicalFlight_vanishes_uniformly hE η hη
  refine ⟨e,he,?_⟩
  intro z hz l hl eq
  dsimp only
  have pos : 0<w.flight z/l := div_pos (by linarith [w.late z]) hl
  have short := small z hz
  rw [w.physicalFlight_eq hl eq,abs_of_pos pos] at short
  refine ⟨pos,short,?_⟩
  intro s hs
  have r := radius_speed 1 (restore l ![(z.1:ℝ),0,1,0]) 0 s
  simp only [solution_zero,abs_one,one_mul,sub_zero] at r
  have sl : |s|≤w.flight z/l := by
    rw [abs_of_nonpos hs.2,neg_le]
    simpa only [neg_div] using hs.1
  exact r.trans_lt (sl.trans_lt short)

end ClosedSimilarity.GlobalSupport.MovingSeam.PrescribedSection
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.PrescribedSection.uniform_short_physical_arc
