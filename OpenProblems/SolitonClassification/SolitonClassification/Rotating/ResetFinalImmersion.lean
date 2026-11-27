import SolitonClassification.Rotating.ResetGridClosure
import SolitonClassification.Rotating.ResetCompletePlus
import SolitonClassification.Rotating.ResetCompleteMinus

namespace SolitonClassification.Rotating.IntegerTarget
open DyadicReset
theorem rotating_immersion_of_turning_minus_one :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 :=
  immersion_from_indexed_rows CompletePlus.atRow CompleteMinus.atRow
    CompletePlus.range CompleteMinus.range
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.rotating_immersion_of_turning_minus_one
