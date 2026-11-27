import SolitonClassification.UnboundedClosedExpanders
import SolitonClassification.PhysicalMatchedMarker

noncomputable section
open Set Filter
open scoped Topology
namespace ClosedSimilarity.GlobalSupport.MovingSeam

/-- All data refer to one physical shooting match per index, including the
actual arclength between the incoming section and the reflection seam. -/
structure MatchedSequence {H E B : ℝ} (c : CentreChart H E B) (w : WindingChart H E)
    (f : w.Flight) where
  marker : ℕ → Ici B
  seamParameter : ℕ → ChartDomain E
  unbounded_marker : Tendsto (fun i => (marker i : ℝ)) atTop atTop
  flight_positive : ∀ i, 0 < f.length (seamParameter i)
  seam_positive : ∀ i, 0 < c.time (marker i) + f.length (seamParameter i)
  reflection : ∀ i, let s := c.time (marker i) + f.length (seamParameter i)
    let u := solution 1 ![0,(marker i:ℝ),0,0] s
    u 1 = 0 ∧ u 3 = 0

theorem CentreChart.exists_matched_sequence {H E B : ℝ} (c : CentreChart H E B)
    (w : WindingChart H E) (f : w.Flight) : Nonempty (MatchedSequence c w f) := by
  have found (i : ℕ) := c.arbitrarily_large_matches w (max B (i:ℝ)) (le_max_left ..)
  choose b hb z n eps angle impact using found
  have data (i : ℕ) := matched_quarter_at_flight c w f (b i) (z i) (n i)
    (eps i) (angle i) (impact i)
  have grow : Tendsto (fun i => (b i:ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun i => (le_max_right B (i:ℝ)).trans (hb i)) tendsto_natCast_atTop_atTop
  exact ⟨⟨b,z,grow,fun i => (data i).1,fun i => (data i).2.1,fun i => (data i).2.2⟩⟩

/-- Compactness of the seam parameter rectangle gives one physical
arclength bound for all matched shots. -/
theorem WindingChart.Flight.bounded_length {H E : ℝ} {w : WindingChart H E}
    (f : w.Flight) : ∃ M ≥ (1:ℝ), ∀ z, |f.length z| ≤ M := by
  obtain ⟨A,hA⟩ := (isCompact_range f.continuous_length.abs).bddAbove
  exact ⟨max 1 A, le_max_left .., fun z => (hA ⟨z,rfl⟩).trans (le_max_right ..)⟩

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.CentreChart.exists_matched_sequence
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.WindingChart.Flight.bounded_length
