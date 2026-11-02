import Lemniscate.EvenCouplingScalarBounds
import Lemniscate.PeriodicEvenHead
import Lemniscate.EvenFactorData

/-! Match the analytic weights to the checked finite energy estimate, then
bound the actual symmetric coefficient entries with those same weights. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate

def evenModePenalty (n : ℤ) : ℚ :=
  if n.natAbs ≤ 2 then 1/10 else (n:ℚ)^4/100

theorem even_mode_penalty_lower (n : ℤ) : (1/16:ℚ) ≤ evenModePenalty n := by
  by_cases hn : n.natAbs ≤ 2
  · norm_num [evenModePenalty,if_pos hn]
  · have ha : (3:ℚ) ≤ |(n:ℚ)| := by
      have h : 3 ≤ n.natAbs := by omega
      simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (3:ℚ) ≤ (n.natAbs:ℚ) by exact_mod_cast h)
    have h2 := pow_le_pow_left₀ (by norm_num : (0:ℚ) ≤ 3) ha 2
    norm_num only [sq_abs] at h2
    have h4 := pow_le_pow_left₀ (by norm_num : (0:ℚ) ≤ 9) h2 2
    simp only [evenModePenalty,if_neg hn]
    nlinarith only [h2,h4]

set_option maxRecDepth 100000 in
theorem even_factor_penalty_values :
    ∀ i : Fin 31, evenFactorPenalty i = evenModePenalty (evenHeadFrequency i) := by
  decide +kernel

theorem even_symmetric_off_scalar_symm (r : ℝ) (j : Fin 3) (x y : ℝ) :
    evenSymmetricOffScalar r j x y = evenSymmetricOffScalar r j y x := by
  fin_cases j <;>
    simp only [evenSymmetricOffScalar,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_one] <;> ring

variable (T : ℝ) [Fact (0 < T)]

theorem circle_bloch_symmetric_entry_square_bound (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x)
    (hs : ∀ n : ℤ, fourierCoeff h (-n) = fourierCoeff h n)
    (hc : ∀ j : ℕ, fourierCoeff h (2*(j:ℤ)) =
      (fourierCoefficient thetaParameter nome j:ℂ))
    (hr : (2*Real.pi/T)^2 ≤ 18/25) (n m : ℤ) (hn : 16 ≤ n.natAbs) (hm : m.natAbs ≤ 15) :
    (∑ j : Fin 3,
      ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*n)‖^2 /
        ((evenModePenalty (2*m):ℝ)*(2*(n:ℝ))^4)) ≤
      (if 12 ≤ m.natAbs then (3/8:ℝ) else 15000)*‖fourierCoeff h (2*n-2*m)‖^2 := by
  have hne : n ≠ m := by intro he; subst n; omega
  have hnorm (j : Fin 3) :
      ‖fourierCoeff (circleBlochSymmetricCoefficient T h h₁ h₂ j (circleFourierH4 T (2*m))) (2*n)‖^2 =
        (evenSymmetricOffScalar ((2*Real.pi/T)^2) j (2*(m:ℝ)) (2*(n:ℝ)))^2*
          ‖fourierCoeff h (2*n-2*m)‖^2 := by
    rw [circle_bloch_symmetric_off_diagonal T h h₁ h₂ hh hh₁ hreal h₁real h₂real hs hc j n m hne,
      norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,even_symmetric_off_scalar_symm]
  have hnR : 32 ≤ |(2*(n:ℝ))| := by
    have h : (16:ℝ) ≤ |(n:ℝ)| := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (16:ℝ) ≤ (n.natAbs:ℝ) by exact_mod_cast hn)
    rw [abs_mul,show |(2:ℝ)| = 2 by norm_num]
    linarith only [h]
  have hδ : (1/16:ℝ) ≤ (evenModePenalty (2*m):ℝ) := by
    have hd : ((1/16:ℚ):ℝ) ≤ (evenModePenalty (2*m):ℝ) :=
      Rat.cast_le.mpr (even_mode_penalty_lower (2*m))
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hd
    exact hd
  have hδ0 : 0 < (evenModePenalty (2*m):ℝ) := by linarith only [hδ]
  have hn0 : (n:ℝ) ≠ 0 := by
    have hnz : n ≠ 0 := by intro hz; simp only [hz,Int.natAbs_zero] at hn; omega
    exact_mod_cast hnz
  have hden : 0 < (evenModePenalty (2*m):ℝ)*(2*(n:ℝ))^4 := by positivity
  simp only [hnorm,← Finset.sum_div,← Finset.sum_mul]
  apply (div_le_iff₀ hden).mpr
  by_cases hlarge : 12 ≤ m.natAbs
  · rw [if_pos hlarge]
    have hmR : 24 ≤ |(2*(m:ℝ))| := by
      have h : (12:ℝ) ≤ |(m:ℝ)| := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (12:ℝ) ≤ (m.natAbs:ℝ) by exact_mod_cast hlarge)
      rw [abs_mul,show |(2:ℝ)| = 2 by norm_num]
      linarith only [h]
    have hsmall : ¬(2*m).natAbs ≤ 2 := by
      have he : (2*m).natAbs = 2*m.natAbs := by simp [Int.natAbs_mul]
      rw [he]
      omega
    have hpen : (evenModePenalty (2*m):ℝ) = (2*(m:ℝ))^4/100 := by
      simp only [evenModePenalty,if_neg hsmall]
      push_cast
      ring
    rw [hpen]
    have h := mul_le_mul_of_nonneg_right
      (even_symmetric_large_scalar_bound ((2*Real.pi/T)^2) (2*(m:ℝ)) (2*(n:ℝ))
        (sq_nonneg _) hr hmR hnR) (sq_nonneg ‖fourierCoeff h (2*n-2*m)‖)
    convert h using 1 <;> ring
  · rw [if_neg hlarge]
    have hmR : |(2*(m:ℝ))| ≤ 22 := by
      have h : |(m:ℝ)| ≤ 11 := by
        simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (m.natAbs:ℝ) ≤ 11 by exact_mod_cast (show m.natAbs ≤ 11 by omega))
      rw [abs_mul,show |(2:ℝ)| = 2 by norm_num]
      linarith only [h]
    have h := mul_le_mul_of_nonneg_right
      (even_symmetric_small_scalar_bound ((2*Real.pi/T)^2) (2*(m:ℝ)) (2*(n:ℝ)) (evenModePenalty (2*m):ℝ)
        (sq_nonneg _) hr hmR hnR hδ) (sq_nonneg ‖fourierCoeff h (2*n-2*m)‖)
    convert h using 1 <;> ring

end Lemniscate
