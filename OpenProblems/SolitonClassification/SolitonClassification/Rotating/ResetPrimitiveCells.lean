import SolitonClassification.Rotating.ResetOnlyCells
import SolitonClassification.Rotating.IntegerTurningPeriod

namespace SolitonClassification.Rotating.IntegerTarget
open DyadicReset

/-- All remaining assumptions on the one-turn example are explicit finite
polynomial tests. Its stated length is the shortest position period. -/
theorem primitive_immersion_from_polynomial_cells
    (P M : Fin 4000→PackedCell) (hp : CellTests Middle.hn GridPlus.atNode P)
    (hm : CellTests (-Middle.hn) GridMinus.atNode M) :
    ∃c∈cube, ∃I : WindingOneImmersion (c 4) (2*c 2),
      60<2*c 2 ∧ 2*c 2<62 ∧ 1/10<c 4 ∧ c 4<11/100 ∧ 7<I.k 0 ∧
      (∃s, I.k s<0) ∧ c 4*(I.x 0*deriv I.x 0+I.y 0*deriv I.y 0)≠0 ∧
      IsLeast {h : ℝ | 0<h ∧ Function.Periodic I.x h ∧ Function.Periodic I.y h} (2*c 2) := by
  obtain ⟨c,hc,I,A,B,C,D,E,F,G⟩ := immersion_from_polynomial_cells P M hp hm
  exact ⟨c,hc,I,A,B,C,D,E,F,G,I.least_positive_period (by linarith)⟩
end SolitonClassification.Rotating.IntegerTarget
#print axioms SolitonClassification.Rotating.IntegerTarget.primitive_immersion_from_polynomial_cells
