import Lemniscate.WeightedCosineTail

/-! Connect the nine exact rational comparisons to full infinite weighted rows
of the concrete coefficient-defined cosine matrix. The identification of this
matrix with the geometric differential operator is not asserted here. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def cosineOffRow (j k : ℕ) : ℝ :=
  if k = j then 0 else |cosineMatrixEntry thetaParameter nome j k| *
    ((weight k:ℝ)/(weight j:ℝ))

theorem cosine_off_row_enclosure (j k : ℕ) :
    cosineOffRow j k ≤
      ((if k = j then 0 else absUpper (cosineEntry j k)*weight k/weight j : ℚ):ℝ) := by
  by_cases h : k = j
  · simp [cosineOffRow, h]
  · simp only [cosineOffRow, if_neg h, Rat.cast_mul, Rat.cast_div]
    have hjw : (0:ℝ) < (weight j:ℝ) := by exact_mod_cast weight_pos j
    have hkw : (0:ℝ) < (weight k:ℝ) := by exact_mod_cast weight_pos k
    have he := absUpper_sound _ _ (theta_nome_cosine_matrix_enclosure j k)
    calc
      _ ≤ (absUpper (cosineEntry j k):ℝ)*((weight k:ℝ)/(weight j:ℝ)) :=
        mul_le_mul_of_nonneg_right he (le_of_lt (div_pos hkw hjw))
      _ = _ := by ring

theorem cosine_head_bound (j : ℕ) :
    (∑ k ∈ Finset.range 20, cosineOffRow j k) ≤
      (sumTo 20 (fun k => if k = j then 0 else
        absUpper (cosineEntry j k)*weight k/weight j) : ℝ) := by
  rw [OddArithmetic.sumTo_eq_sum_range, Rat.cast_sum]
  exact Finset.sum_le_sum (fun k _ => cosine_off_row_enclosure j k)

theorem cosine_row_summable_and_bound (j : ℕ) (hj : j < 20) :
    Summable (cosineOffRow j) ∧
    cosineMatrixEntry thetaParameter nome j j + ∑' k : ℕ, cosineOffRow j k ≤
      (finiteRow j : ℝ) := by
  have heq : (fun n : ℕ => cosineOffRow j (n+20)) =
      (fun n : ℕ => |cosineMatrixEntry thetaParameter nome j (j+(n+(20-j)))| *
        ((weight (j+(n+(20-j))):ℝ)/(weight j:ℝ))) := by
    funext n
    rw [show j+(n+(20-j)) = n+20 by omega]
    simp only [cosineOffRow, if_neg (show n+20 ≠ j by omega)]
  have ht := cosine_weighted_tail_bound j (20-j) (by omega) (by omega)
  rw [← heq] at ht
  have hs : Summable (cosineOffRow j) := (summable_nat_add_iff 20).mp ht.1
  refine ⟨hs, ?_⟩
  have hd := (theta_nome_cosine_matrix_enclosure j j).2
  calc
    _ = cosineMatrixEntry thetaParameter nome j j +
        ((∑ k ∈ Finset.range 20, cosineOffRow j k)+
          ∑' n : ℕ, cosineOffRow j (n+20)) := by
      rw [hs.sum_add_tsum_nat_add 20]
    _ ≤ ((cosineEntry j j).hi:ℝ) +
        ((sumTo 20 (fun k => if k = j then 0 else
          absUpper (cosineEntry j k)*weight k/weight j):ℝ)+
          (weightedEntryTailBound j (20-j):ℝ)) :=
      add_le_add hd (add_le_add (cosine_head_bound j) ht.2)
    _ = _ := by
      simp only [finiteRow, weightedEntryTailBound, tailWeightFactor,
        Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
        Rat.cast_ofNat, Rat.cast_natCast]
      ring

theorem cosine_low_rows_dissipative (j : Fin 9) :
    Summable (cosineOffRow j.val) ∧
    cosineMatrixEntry thetaParameter nome j.val j.val +
      ∑' k : ℕ, cosineOffRow j.val k < -(21/4:ℝ) := by
  have h := cosine_row_summable_and_bound j.val (by omega)
  refine ⟨h.1, h.2.trans_lt ?_⟩
  have hc := (Rat.cast_lt (K := ℝ)).mpr (cosine_rows j)
  simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using hc

end Lemniscate.CoarseArithmetic
