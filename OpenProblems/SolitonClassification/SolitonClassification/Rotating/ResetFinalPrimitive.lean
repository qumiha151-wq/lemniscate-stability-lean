import SolitonClassification.Rotating.IntegerHullIndexed
import SolitonClassification.Rotating.ResetCompletePlus
import SolitonClassification.Rotating.ResetCompleteMinus

namespace SolitonClassification.Rotating.IntegerTarget
open DyadicReset

/-- A noncircular primitive closed rotating and expanding immersion. Its
actual image contains the similarity center strictly inside its convex hull. -/
theorem primitive_rotating_immersion_with_center_disk :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) ∧
      (∀w : ℝ × ℝ, |w.1|≤1/20 → |w.2|≤1/20 → w∈convexHull ℝ (Set.range (fun s => (I.x s,I.y s)))) :=
  square_immersion_from_indexed_rows CompletePlus.atRow CompleteMinus.atRow
    CompletePlus.range CompleteMinus.range

end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.primitive_rotating_immersion_with_center_disk
