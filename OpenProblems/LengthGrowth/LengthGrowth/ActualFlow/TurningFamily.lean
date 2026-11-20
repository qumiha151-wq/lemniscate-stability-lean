import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Geometric net turning of disjoint subarcs. Intersections at endpoints
are allowed and the orientation of each excursion may be chosen separately. -/
noncomputable section
open Set MeasureTheory
namespace LengthGrowth.ActualFlow.MacroscopicTurning

def ExcursionFamily (k : ℝ → ℝ) (a b : ℝ) (m : ℕ) : Prop :=
  ∃ U : Finset (ℝ × ℝ), U.card = m ∧
    (∀ J∈U, a≤J.1 ∧ J.1<J.2 ∧ J.2≤b ∧ 1/4 ≤ |∫ s in J.1..J.2, k s|) ∧
    (∀ I∈U, ∀ J∈U, I≠J → Disjoint (Ioo I.1 I.2) (Ioo J.1 J.2))

end LengthGrowth.ActualFlow.MacroscopicTurning
