import Lemniscate.PeriodicCosineJets

/-! The actual L2 matrix entries of the classical differential expression in
the normalized even-cosine basis, including the exceptional zero mode. -/
namespace Lemniscate
open Complex MeasureTheory

variable (T : ℝ) [Fact (0 < T)]

theorem circle_symmetric_entry_neg (h : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (n m : ℤ) :
    circleSymmetricFourierEntry T h (-n) (-m) = circleSymmetricFourierEntry T h n m := by
  have hi : -n- -m = -(n-m) := by omega
  unfold circleSymmetricFourierEntry
  rw [hi, hs]
  simp only [neg_inj, Int.cast_neg]
  push_cast
  ring

theorem circle_symmetric_entry_neg_left (h : C(AddCircle T, ℂ))
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (n m : ℤ) :
    circleSymmetricFourierEntry T h (-n) m = circleSymmetricFourierEntry T h n (-m) := by
  simpa only [neg_neg] using circle_symmetric_entry_neg T h hs n (-m)

theorem evenCosineFactor_twice : 2*evenCosineFactor = (Real.sqrt 2:ℂ) := by
  have hn : Real.sqrt (2:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have he : 2*(1/Real.sqrt (2:ℝ)) = Real.sqrt 2 := by
    field_simp [hn]
    nlinarith
  unfold evenCosineFactor
  exact_mod_cast he

theorem circle_cosine_matrix_positive_pairing (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    inner ℂ (circleEvenCosineMode T j)
      (circleContinuousL2 T (circleSymmetricCosineMode T h h₁ h₂ k)) =
        circleSymmetricFourierEntry T h (2*(j:ℤ)) (2*(k:ℤ)) +
        circleSymmetricFourierEntry T h (2*(j:ℤ)) (-(2*(k:ℤ))) := by
  rw [circle_cosine_inner_fourier]
  simp only [if_neg (Nat.ne_of_gt hj), circle_symmetric_cosine_fourier T h h₁ h₂ hh hh₁,
    if_neg (Nat.ne_of_gt hk)]
  rw [circle_symmetric_entry_neg T h hs, circle_symmetric_entry_neg_left T h hs]
  calc
    _ = (evenCosineFactor*(evenCosineFactor*2))*
        (circleSymmetricFourierEntry T h (2*(j:ℤ)) (2*(k:ℤ)) +
          circleSymmetricFourierEntry T h (2*(j:ℤ)) (-(2*(k:ℤ)))) := by ring
    _ = _ := by rw [evenCosineFactor_normalization, one_mul]

theorem circle_cosine_matrix_positive (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    inner ℂ (circleEvenCosineMode T j)
      (circleContinuousL2 T (circleSymmetricCosineMode T h h₁ h₂ k)) =
      ((-4*(2*Real.pi/T)^4*(2*(k:ℝ))^4-42:ℝ):ℂ)*(if j = k then 1 else 0) +
      (((2*Real.pi/T)^2*(45*(2*(j:ℝ))*(2*(k:ℝ)) -
        (15/4:ℝ)*(2*(j:ℝ)-2*(k:ℝ))^2):ℝ):ℂ)*fourierCoeff h (2*(j:ℤ)-2*(k:ℤ)) -
      (((2*Real.pi/T)^2*(45*(2*(j:ℝ))*(2*(k:ℝ)) +
        (15/4:ℝ)*(2*(j:ℝ)+2*(k:ℝ))^2):ℝ):ℂ)*fourierCoeff h (2*(j:ℤ)+2*(k:ℤ)) := by
  rw [circle_cosine_matrix_positive_pairing T h h₁ h₂ hh hh₁ hs j k hj hk]
  have hcross : 2*(j:ℤ) ≠ -(2*(k:ℤ)) := by omega
  have heq : (2*(j:ℤ) = 2*(k:ℤ)) ↔ j = k := by omega
  unfold circleSymmetricFourierEntry
  simp only [if_neg hcross, heq, mul_zero, sub_neg_eq_add]
  push_cast
  ring

theorem circle_cosine_matrix_zero_zero (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂) :
    inner ℂ (circleEvenCosineMode T 0)
      (circleContinuousL2 T (circleSymmetricCosineMode T h h₁ h₂ 0)) = -42 := by
  rw [circle_cosine_inner_fourier]
  simp only [ite_true, circle_symmetric_cosine_fourier T h h₁ h₂ hh hh₁]
  simp [circleSymmetricFourierEntry]

theorem circle_cosine_matrix_zero_positive (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (k : ℕ) (hk : 0 < k) :
    inner ℂ (circleEvenCosineMode T 0)
      (circleContinuousL2 T (circleSymmetricCosineMode T h h₁ h₂ k)) =
        (-(15/4:ℂ))*(Real.sqrt 2:ℂ)*(((2*Real.pi/T)^2*(2*(k:ℝ))^2:ℝ):ℂ)*
          fourierCoeff h (2*(k:ℤ)) := by
  rw [circle_cosine_inner_fourier]
  simp only [ite_true, circle_symmetric_cosine_fourier T h h₁ h₂ hh hh₁,
    if_neg (Nat.ne_of_gt hk)]
  have hsym : circleSymmetricFourierEntry T h 0 (-(2*(k:ℤ))) =
      circleSymmetricFourierEntry T h 0 (2*(k:ℤ)) := by
    simpa only [neg_zero] using circle_symmetric_entry_neg T h hs 0 (2*(k:ℤ))
  rw [hsym]
  have hn : (0:ℤ) ≠ 2*(k:ℤ) := by omega
  unfold circleSymmetricFourierEntry
  simp only [if_neg hn, zero_sub, hs, Int.cast_zero, zero_mul, mul_zero, zero_add,
    sub_zero, neg_sq]
  rw [← evenCosineFactor_twice]
  push_cast
  ring

theorem circle_cosine_matrix_positive_zero (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n) (j : ℕ) (hj : 0 < j) :
    inner ℂ (circleEvenCosineMode T j)
      (circleContinuousL2 T (circleSymmetricCosineMode T h h₁ h₂ 0)) =
        (-(15/4:ℂ))*(Real.sqrt 2:ℂ)*(((2*Real.pi/T)^2*(2*(j:ℝ))^2:ℝ):ℂ)*
          fourierCoeff h (2*(j:ℤ)) := by
  rw [circle_cosine_inner_fourier]
  simp only [if_neg (Nat.ne_of_gt hj), circle_symmetric_cosine_fourier T h h₁ h₂ hh hh₁,
    ite_true]
  have hsym : circleSymmetricFourierEntry T h (-(2*(j:ℤ))) 0 =
      circleSymmetricFourierEntry T h (2*(j:ℤ)) 0 := by
    simpa only [neg_zero] using circle_symmetric_entry_neg T h hs (2*(j:ℤ)) 0
  rw [hsym]
  have hn : 2*(j:ℤ) ≠ 0 := by omega
  unfold circleSymmetricFourierEntry
  simp only [if_neg hn, sub_zero, Int.cast_zero, zero_mul, mul_zero, zero_add,
    zero_pow (by norm_num : (4:ℕ) ≠ 0)]
  rw [← evenCosineFactor_twice]
  push_cast
  ring

end Lemniscate
