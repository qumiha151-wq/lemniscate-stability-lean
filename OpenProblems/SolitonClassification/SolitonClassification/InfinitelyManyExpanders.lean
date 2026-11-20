import SolitonClassification.DistinctExpanderFamily
import SolitonClassification.UnboundedClosedExpanders

namespace ClosedSimilarity.GlobalSupport.MovingSeam
open ReflectedArc

/-- Infinitely many smooth closed zero-turn expanders remain geometrically
    distinct after changes of parameter, finite covers and plane similarities. -/
theorem infinitely_many_inequivalent_zero_turn_expanders :
    ∃ family : ℕ → MarkedClosedExpander,
      StrictMono (fun n => (family n).curve.peakSlope) ∧
      (∀ i j : ℕ, i≠j → IsEmpty (GeometricSimilarity (family i).curve (family j).curve)) :=
  distinct_family_of_unbounded unbounded_closed_zero_turn_expanders

end ClosedSimilarity.GlobalSupport.MovingSeam
#print axioms ClosedSimilarity.GlobalSupport.MovingSeam.infinitely_many_inequivalent_zero_turn_expanders
