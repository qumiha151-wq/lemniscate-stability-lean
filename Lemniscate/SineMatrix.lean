import Lemniscate.SineArithmetic
import Lemniscate.MatrixTailSeries

/-! The actual coefficient-defined sine matrix and soundness of its interval
entries. Index j represents the positive even frequency 2j; row zero is not
used to represent a sine basis function. -/
namespace Lemniscate.CoarseArithmetic

noncomputable def sineMatrixEntry (r q : ℝ) (j k : ℕ) : ℝ :=
  let n : ℝ := 2*(j:ℝ)
  let m : ℝ := 2*(k:ℝ)
  let nonconstant := r*
    (fourierCoefficient r q (j-k+(k-j))*(45*n*m-(15/4:ℝ)*(n-m)^2)+
      fourierCoefficient r q (j+k)*(45*n*m+(15/4:ℝ)*(n+m)^2))
  if j = k then nonconstant+(-4*r^2*n^4-42) else nonconstant

theorem sine_matrix_enclosure (r q : ℝ) (j k : ℕ)
    (hr : Contains ⟨rlo,rhi⟩ r) (hq : Contains ⟨qlo,qhi⟩ q) :
    Contains (sineEntry j k) (sineMatrixEntry r q j k) := by
  have hminus := scale_sound _ _
    (45*(2*(j:ℚ))*(2*(k:ℚ))-(15/4:ℚ)*(2*(j:ℚ)-2*(k:ℚ))^2)
    (fourier_enclosure r q (j-k+(k-j)) hr hq)
  have hplus := scale_sound _ _
    (45*(2*(j:ℚ))*(2*(k:ℚ))+(15/4:ℚ)*(2*(j:ℚ)+2*(k:ℚ))^2)
    (fourier_enclosure r q (j+k) hr hq)
  have hnonconstant := mul_sound _ _ _ _ hr (add_sound _ _ _ _ hminus hplus)
  by_cases heq : j = k
  · have h := add_sound _ _ _ _ hnonconstant (cosine_diagonal_enclosure r (2*(j:ℚ)) hr)
    simpa only [sineEntry, sineMatrixEntry, if_pos heq, Rat.cast_neg, Rat.cast_mul,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_add, Rat.cast_sub,
      Rat.cast_natCast] using h
  · simpa only [sineEntry, sineMatrixEntry, if_neg heq, Rat.cast_neg, Rat.cast_mul,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_add, Rat.cast_sub,
      Rat.cast_natCast] using hnonconstant

theorem theta_nome_sine_matrix_enclosure (j k : ℕ) :
    Contains (sineEntry j k) (sineMatrixEntry thetaParameter nome j k) :=
  sine_matrix_enclosure _ _ j k actual_nome_theta_r_bounds coarse_nome_bounds

theorem sine_matrix_symmetric (r q : ℝ) (j k : ℕ) :
    sineMatrixEntry r q j k = sineMatrixEntry r q k j := by
  by_cases heq : j = k
  · subst k; rfl
  · simp only [sineMatrixEntry, if_neg heq, if_neg (Ne.symm heq)]
    rw [Nat.add_comm k j, Nat.add_comm (k-j) (j-k)]
    ring

theorem sine_off_diagonal (r q : ℝ) (j k : ℕ) (hjk : j ≠ k) :
    sineMatrixEntry r q j k = positiveFrequencyEntry r q (-1) j k := by
  simp only [sineMatrixEntry, if_neg hjk, positiveFrequencyEntry]
  ring

theorem sine_upper_tail (j k : ℕ) (hjk : j < k) :
    |sineMatrixEntry thetaParameter nome j k| ≤
      (C:ℝ)*(2*(j:ℝ)+((k-j:ℕ):ℝ))^2*((k-j:ℕ):ℝ)*(qb:ℝ)^(k-j) := by
  rw [sine_off_diagonal _ _ j k (Nat.ne_of_lt hjk)]
  exact positive_frequency_upper_tail (-1) j k (by norm_num) hjk

theorem sine_tail_bound (j L : ℕ) (hL : 0 < L) :
    Summable (fun n : ℕ => |sineMatrixEntry thetaParameter nome j (j+(n+L))|) ∧
    (∑' n : ℕ, |sineMatrixEntry thetaParameter nome j (j+(n+L))|) ≤
      (entryTailBound j L:ℝ) := by
  have he : (fun n : ℕ => |sineMatrixEntry thetaParameter nome j (j+(n+L))|) =
      (fun n : ℕ => |positiveFrequencyEntry thetaParameter nome (-1) j (j+(n+L))|) := by
    funext n
    rw [sine_off_diagonal _ _ j (j+(n+L)) (by omega)]
  rw [he]
  exact positive_frequency_tail_bound (-1) j L (by norm_num) hL

theorem sine_first_diagonal_bound : sineMatrixEntry thetaParameter nome 1 1 < -12 := by
  apply (theta_nome_sine_matrix_enclosure 1 1).2.trans_lt
  exact_mod_cast sine_first_diagonal_certificate

end Lemniscate.CoarseArithmetic
