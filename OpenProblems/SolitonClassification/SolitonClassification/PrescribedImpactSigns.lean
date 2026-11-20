import SolitonClassification.PrescribedSeamSections

noncomputable section
open Set Filter Metric
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam

def PrescribedSection.sectionImpact {a b H E : ℝ} (w : PrescribedSection a b H E)
    (c : Icc a b) (e : Icc (0:ℝ) E) := impact (shot (w.drive (c,e)) c (-w.flight (c,e)))

/-- The strict endpoint signs persist on a nonzero interval of *incoming*
    scales after imposing both the actual physical radius and the corrected
    height. The same interval works for both endpoint shots. -/
theorem PrescribedSection.impact_strip {a b H E α β : ℝ} (w : PrescribedSection a b H E)
    (hab : a≤b) (ep : 0<E)
    (lo : ∀t≥20, seamImpact a t<α) (hi : ∀t≥20, β<seamImpact b t) :
    ∃D∈Ioc 0 E, ∀e : Icc (0:ℝ) E, (e:ℝ)≤D →
      w.sectionImpact ⟨a,le_rfl,hab⟩ e < α ∧ β < w.sectionImpact ⟨b,hab,le_rfl⟩ e := by
  let L : Icc a b := ⟨a,le_rfl,hab⟩
  let R : Icc a b := ⟨b,hab,le_rfl⟩
  let O : Icc (0:ℝ) E := ⟨0,le_rfl,ep.le⟩
  have fr (c : Icc a b) : w.sectionImpact c O=seamImpact c (w.flight (c,O)) := by
    unfold sectionImpact
    rw [w.frozen (c,O) rfl,frozen_impact]
    obtain ⟨_,v,_,q⟩ := seam_initial c
    exact ((seam c).seam_impact_radial_parity v q _).1
  have cL : Continuous (w.sectionImpact L) := w.continuous_impact.comp (continuous_const.prodMk continuous_id)
  have cR : Continuous (w.sectionImpact R) := w.continuous_impact.comp (continuous_const.prodMk continuous_id)
  have l : w.sectionImpact L O<α := (fr L).trans_lt (lo _ (w.late (L,O)).le)
  have r : β<w.sectionImpact R O := (hi _ (w.late (R,O)).le).trans_eq (fr R).symm
  obtain ⟨δ,hδ,h⟩ := Metric.mem_nhds_iff.mp
    (((cL.tendsto O).eventually (eventually_lt_nhds l)).and ((cR.tendsto O).eventually (eventually_gt_nhds r)))
  refine ⟨min E (δ/2),⟨lt_min ep (by positivity),min_le_left ..⟩,?_⟩
  intro e he
  apply h
  change |(e:ℝ)-(O:ℝ)|<δ
  rw [show (O:ℝ)=0 from rfl,sub_zero,abs_of_nonneg e.property.1]
  exact (he.trans (min_le_right ..)).trans_lt (half_lt_self hδ)

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.PrescribedSection.impact_strip
