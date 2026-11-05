import Lemniscate.ShortSchurFiniteCertificate

/-! Real inequalities for the actual finite coupling and high blocks.
The explicitly retained tails are the ones used in the infinite-mode step. -/
namespace Lemniscate.CoarseArithmetic
open Finset

def shortFiniteHighTail (i : Fin 22) : ℚ :=
  if (shortHighHalfFrequency i).natAbs≤7 then shortInsideRowTail else
    2*shortHighOffCoefficient*tail1 qb (15-(shortHighHalfFrequency i).natAbs)

theorem short_finite_cross_square (j : Fin 5) :
    (∑ i : Fin 7, ∑ k : Fin 22, |shortCrossEntry j i (shortHighHalfFrequency k)|^2) +
      (shortCrossTailSquare:ℝ) ≤ (1/16:ℝ) := by
  have hsum : (∑ i : Fin 7, ∑ k : Fin 22, |shortCrossEntry j i (shortHighHalfFrequency k)|^2) ≤
      (shortFiniteCrossSquare j:ℝ) := by
    unfold shortFiniteCrossSquare
    simp only [Rat.cast_sum, Rat.cast_pow]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro k _
    exact pow_le_pow_left₀ (abs_nonneg _) (absUpper_sound _ _ (short_finite_cross_entry_sound j i k)) 2
  have hnum : ((shortFiniteCrossSquare j+shortCrossTailSquare:ℚ):ℝ) < (1/16:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (short_finite_cross_square_bound j)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  calc
    _ ≤ (shortFiniteCrossSquare j:ℝ)+(shortCrossTailSquare:ℝ) := add_le_add hsum le_rfl
    _ = ((shortFiniteCrossSquare j+shortCrossTailSquare:ℚ):ℝ) := by rw [Rat.cast_add]
    _ ≤ 1/16 := hnum.le

theorem short_finite_high_row (j : Fin 5) (i : Fin 22) :
    shortHighEntry j (shortHighHalfFrequency i) (shortHighHalfFrequency i) +
      (∑ k : Fin 22, if k=i then 0 else
        |shortHighEntry j (shortHighHalfFrequency i) (shortHighHalfFrequency k)|) +
      (shortFiniteHighTail i:ℝ) ≤ -(5/4:ℝ) := by
  let M := integerMatrixInterval (shortEData j)
  have hrow : shortHighEntry j (shortHighHalfFrequency i) (shortHighHalfFrequency i) +
      (∑ k : Fin 22, if k=i then 0 else
        |shortHighEntry j (shortHighHalfFrequency i) (shortHighHalfFrequency k)|) ≤
      ((M i i).hi:ℝ)+(∑ k : Fin 22, if k=i then 0 else (absUpper (M i k):ℝ)) := by
    apply add_le_add (short_finite_high_entry_sound j i i).2
    apply Finset.sum_le_sum
    intro k _
    by_cases hki : k=i
    · simp only [if_pos hki, le_refl]
    · simp only [if_neg hki]
      exact absUpper_sound _ _ (short_finite_high_entry_sound j i k)
  have hcast : ((M i i).hi:ℝ)+(∑ k : Fin 22, if k=i then 0 else (absUpper (M i k):ℝ)) +
      (shortFiniteHighTail i:ℝ) = (shortFiniteHighRow j i:ℝ) := by
    unfold shortFiniteHighRow shortFiniteHighTail
    simp only [Rat.cast_add, Rat.cast_sum]
    congr 2
    · apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k=i <;> simp only [hki, ite_true, ite_false, Rat.cast_zero]
      rfl
  have hnum : (shortFiniteHighRow j i:ℝ) < -(5/4:ℝ) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr (short_finite_high_rows j i)
    simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using h
  exact ((add_le_add hrow (le_refl (shortFiniteHighTail i:ℝ))).trans_eq hcast).trans hnum.le

end Lemniscate.CoarseArithmetic
