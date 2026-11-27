import SolitonClassification.ManyFastAxisCrossings
import SolitonClassification.FullQuarterCapture
import SolitonClassification.MatchedQuarterProfiles
import SolitonClassification.MatchedRayLimit

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.CrossingResponse
open GlobalSupport GlobalSupport.MovingSeam ReflectedArc

/-- Fixed-target incidence data on an actual first quarter, in the frame of
its initial tangent. Both components of the tangent relative to the seam
are nonzero. The signed incidence test covers the entire quarter. -/
structure QuarterVisits (b S β : ℝ) (N : ℕ) where
  time : Fin N → ℝ
  distinct : Function.Injective (fun i => Y ((b^2)⁻¹) (time i))
  visit : ∀ i, let e := (b^2)⁻¹; let r := time i
    r∈Ioo 0 (Real.sqrt b*S) ∧ 0<Y e r ∧ X e r=β*Y e r ∧
      tx e r-β*ty e r≠0 ∧ β*tx e r+ty e r≠0 ∧
      ∀ t∈Icc (0:ℝ) (Real.sqrt b*S),
        (X e t=X e r → Y e t=Y e r → t=r) ∧ ¬(X e t= -X e r ∧ Y e t= -Y e r)

/-- Arbitrarily large physical centre shots that actually close have
arbitrarily many distinct transverse visits to their own positive seam ray.
On the first quarter each target has a unique preimage and its opposite has
none. No incidence, direction or capture assumptions are imposed. -/
theorem exists_matched_axis_visits (N : ℕ) (A : ℝ) :
    ∃ b>A, 0<b ∧ ∃ S>0, ∃ P : ZeroTurnExpander (4*S) b, ∃ β : ℝ,
      P.cartesianSupport S 1=0 ∧ P.cartesianSupport S 3=0 ∧
      0<Y ((b^2)⁻¹) (Real.sqrt b*S) ∧
      X ((b^2)⁻¹) (Real.sqrt b*S)=β*Y ((b^2)⁻¹) (Real.sqrt b*S) ∧
      Nonempty (QuarterVisits b S β N) := by
  obtain ⟨K,_,rays⟩ := matched_seam_ray_limit
  obtain ⟨H,E,B,high,big,w,c,_,⟨f⟩,⟨a⟩⟩ := exists_physical_shooting_charts_with_geometry K
  obtain ⟨m⟩ := c.exists_matched_sequence w f
  let b := fun i => (m.marker i:ℝ)
  let e := fun i => ((b i)^2)⁻¹
  have pos (i) : 0<b i := m.marker_pos big i
  obtain ⟨slope,late⟩ := rays c w a f high m
  have bounds := late 1 zero_lt_one
  have cap := full_quarter_disk_capture b m.slowEnd pos m.unbounded_marker
    (bounds.mono fun i h u hu => (h u hu).2)
  have cap' (R : ℝ) (hr : 0≤R) : ∃ M : ℝ, ∀ᶠ i in atTop, ∀ t∈Icc (0:ℝ) (m.fastEnd i),
      X (e i) t^2+Y (e i) t^2 ≤ R^2 → t≤M := by
    obtain ⟨M,vis⟩ := cap R hr
    refine ⟨M,?_⟩
    filter_upwards [vis] with i hi
    simpa only [b,m.fastEnd_eq i (pos i)] using hi
  obtain ⟨T,_,hits⟩ := many_unique_quarter_crossings N
  have ep : ∀ᶠ i in atTop, 0<e i := Eventually.of_forall fun i => inv_pos.mpr (pow_pos (pos i) _)
  have selected := hits e m.raySlope m.fastEnd m.fast_parameters_vanish slope ep
    ((m.fast_seams_diverge big a).eventually_ge_atTop T) cap'
  obtain ⟨i,chosen,hb,ray⟩ := (selected.and ((m.unbounded_marker.eventually_gt_atTop A).and bounds)).exists
  obtain ⟨r,inj,info⟩ := chosen
  obtain ⟨P⟩ := m.profiles i
  have endHeight := (ray (m.slowEnd i) ⟨m.slowEnd_large a i (pos i),le_rfl⟩).2
  rw [m.fastEnd_eq i (pos i)] at endHeight
  have positive : 0<Y (e i) (m.fastEnd i) := (div_pos (pos i) (by norm_num : (0:ℝ)<4800)).trans_le endHeight
  have seam := m.reflection i
  refine ⟨b i,hb,pos i,m.quarter i,m.seam_positive i,P,m.raySlope i,?_,?_,positive,?_,?_⟩
  · rw [P.cartesianSupport_eq_solution]; exact seam.1
  · rw [P.cartesianSupport_eq_solution]; exact seam.2
  · exact (div_mul_cancel₀ _ positive.ne').symm
  · exact ⟨⟨r,inj,fun j => (info j).2⟩⟩

end ClosedSimilarity.CrossingResponse
#print axioms ClosedSimilarity.CrossingResponse.exists_matched_axis_visits
