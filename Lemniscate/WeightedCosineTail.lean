import Lemniscate.CosineTail

/-! The paper's actual geometric weights and the complete weighted upper tail.
The cutoff is arbitrary, provided the tail has reached the geometric part of
the weights. This supplies the analytic meaning of the tail in `finiteRow`. -/
namespace Lemniscate.CoarseArithmetic

theorem weight_pos (j : ℕ) : 0 < weight j := by
  match j with
  | 0 => norm_num [weight]
  | 1 => norm_num [weight]
  | 2 => norm_num [weight]
  | k+3 =>
    exact mul_pos (by norm_num) (pow_pos (by norm_num [a]) k)

theorem weight_large (j : ℕ) (hj : 3 ≤ j) :
    weight j = weight 3*(a^j/a^3) := by
  have he : j = (j-3)+3 := by omega
  rw [he]
  simp [weight, pow_add, a] <;> ring

def tailWeightFactor (j : ℕ) : ℚ := weight 3*(a^j/a^3)/weight j

theorem tailWeightFactor_pos (j : ℕ) : 0 < tailWeightFactor j := by
  unfold tailWeightFactor
  exact div_pos (mul_pos (weight_pos 3)
    (div_pos (pow_pos (by norm_num [a]) j) (by norm_num [a]))) (weight_pos j)

theorem weight_ratio_shift (j l : ℕ) (h : 3 ≤ j+l) :
    weight (j+l)/weight j = tailWeightFactor j*a^l := by
  rw [weight_large (j+l) h, pow_add]
  unfold tailWeightFactor
  ring

def weightedEntryTailBound (j L : ℕ) : ℚ :=
  C*tailWeightFactor j*((2*(j:ℚ))^2*tail1 (qb*a) L+
    2*(2*(j:ℚ))*tail2 (qb*a) L+tail3 (qb*a) L)

theorem hasSum_weighted_entry_majorant (j L : ℕ) :
    HasSum (fun n : ℕ =>
      (C:ℝ)*(tailWeightFactor j:ℝ)*(2*(j:ℝ)+((n+L:ℕ):ℝ))^2*
        ((n+L:ℕ):ℝ)*((qb*a:ℚ):ℝ)^(n+L)) (weightedEntryTailBound j L : ℝ) := by
  have hz : ‖((qb*a:ℚ):ℝ)‖ < 1 := by norm_num [qb, a]
  convert! ((((tail1_sound (qb*a) hz L).mul_left ((2*(j:ℝ))^2)).add
    ((tail2_sound (qb*a) hz L).mul_left (2*(2*(j:ℝ))))).add
    (tail3_sound (qb*a) hz L)).mul_left ((C:ℝ)*(tailWeightFactor j:ℝ)) using 1
  · ext n
    ring
  · simp only [weightedEntryTailBound, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_natCast]

theorem cosine_weighted_tail_majorant (j L n : ℕ) (hL : 0 < L) (h3 : 3 ≤ j+L) :
    |cosineMatrixEntry thetaParameter nome j (j+(n+L))| *
        ((weight (j+(n+L)):ℝ)/(weight j:ℝ)) ≤
      (C:ℝ)*(tailWeightFactor j:ℝ)*(2*(j:ℝ)+((n+L:ℕ):ℝ))^2*
        ((n+L:ℕ):ℝ)*((qb*a:ℚ):ℝ)^(n+L) := by
  have hjw : (0:ℝ) < (weight j:ℝ) := by exact_mod_cast weight_pos j
  have hkw : (0:ℝ) < (weight (j+(n+L)):ℝ) := by
    exact_mod_cast weight_pos (j+(n+L))
  have hratio : (weight (j+(n+L)):ℝ)/(weight j:ℝ) =
      (tailWeightFactor j:ℝ)*(a:ℝ)^(n+L) := by
    have h := weight_ratio_shift j (n+L) (by omega)
    exact_mod_cast h
  have hm := mul_le_mul_of_nonneg_right
    (cosine_upper_tail_all j (j+(n+L)) (by omega)) (le_of_lt (div_pos hkw hjw))
  simp only [Nat.add_sub_cancel_left, hratio] at hm
  calc
    _ ≤ (C:ℝ)*(2*(j:ℝ)+((n+L:ℕ):ℝ))^2*((n+L:ℕ):ℝ)*(qb:ℝ)^(n+L)*
        ((tailWeightFactor j:ℝ)*(a:ℝ)^(n+L)) := by
      simpa only [hratio] using hm
    _ = _ := by simp only [Rat.cast_mul, mul_pow]; ring

theorem cosine_weighted_tail_bound (j L : ℕ) (hL : 0 < L) (h3 : 3 ≤ j+L) :
    Summable (fun n : ℕ => |cosineMatrixEntry thetaParameter nome j (j+(n+L))| *
      ((weight (j+(n+L)):ℝ)/(weight j:ℝ))) ∧
    (∑' n : ℕ, |cosineMatrixEntry thetaParameter nome j (j+(n+L))| *
      ((weight (j+(n+L)):ℝ)/(weight j:ℝ))) ≤ (weightedEntryTailBound j L : ℝ) := by
  have hn (n : ℕ) : 0 ≤ |cosineMatrixEntry thetaParameter nome j (j+(n+L))| *
      ((weight (j+(n+L)):ℝ)/(weight j:ℝ)) := by
    have hjw : (0:ℝ) < (weight j:ℝ) := by exact_mod_cast weight_pos j
    have hkw : (0:ℝ) < (weight (j+(n+L)):ℝ) := by
      exact_mod_cast weight_pos (j+(n+L))
    exact mul_nonneg (abs_nonneg _) (le_of_lt (div_pos hkw hjw))
  have hm := fun n => cosine_weighted_tail_majorant j L n hL h3
  have hs := Summable.of_nonneg_of_le hn hm (hasSum_weighted_entry_majorant j L).summable
  refine ⟨hs, ?_⟩
  simpa only [(hasSum_weighted_entry_majorant j L).tsum_eq] using
    hs.tsum_le_tsum hm (hasSum_weighted_entry_majorant j L).summable

end Lemniscate.CoarseArithmetic
