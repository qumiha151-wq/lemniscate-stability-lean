import Lemniscate.SineMatrix
import Lemniscate.GeometricMomentTails
import Lemniscate.SineHilbert

/-! The actual infinite coupling row in the sine sector is an l2 vector with
norm strictly below 63. All terms beyond the first two are included. -/
namespace Lemniscate.CoarseArithmetic
open scoped ENNReal

theorem hasSum_sine_coupling_majorant :
    HasSum (fun n : ℕ => (C:ℝ)^2*((n+3:ℕ):ℝ)^2*(((n+3:ℕ):ℝ)+2)^4*
      (qb:ℝ)^(2*(n+3))) (sineCouplingTail:ℝ) := by
  have hz : ‖((qb^2:ℚ):ℝ)‖ < 1 := by norm_num [qb]
  have h₂ := moment_tail_sound 2 (by omega) (qb^2) hz 3
  have h₃ := moment_tail_sound 3 (by omega) (qb^2) hz 3
  have h₄ := moment_tail_sound 4 (by omega) (qb^2) hz 3
  have h₅ := moment_tail_sound 5 (by omega) (qb^2) hz 3
  have h₆ := moment_tail_sound 6 (by omega) (qb^2) hz 3
  convert! ((((h₆.add (h₅.mul_left 8)).add (h₄.mul_left 24)).add
    (h₃.mul_left 32)).add (h₂.mul_left 16)).mul_left ((C:ℝ)^2) using 1
  · ext n
    simp only [Rat.cast_pow, ← pow_mul]
    ring
  · simp only [sineCouplingTail, Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat]

theorem sine_coupling_tail_bound :
    Summable (fun n : ℕ => (sineMatrixEntry thetaParameter nome 1 (n+4))^2) ∧
    (∑' n : ℕ, (sineMatrixEntry thetaParameter nome 1 (n+4))^2) ≤ (sineCouplingTail:ℝ) := by
  have hm (n : ℕ) : (sineMatrixEntry thetaParameter nome 1 (n+4))^2 ≤
      (C:ℝ)^2*((n+3:ℕ):ℝ)^2*(((n+3:ℕ):ℝ)+2)^4*(qb:ℝ)^(2*(n+3)) := by
    have hb := sine_upper_tail 1 (n+4) (by omega)
    simp only [show n+4-1 = n+3 by omega, Nat.cast_one, mul_one] at hb
    have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hs
    calc
      _ ≤ ((C:ℝ)*(2+((n+3:ℕ):ℝ))^2*((n+3:ℕ):ℝ)*(qb:ℝ)^(n+3))^2 := hs
      _ = _ := by
        simp only [mul_pow, ← pow_mul, Nat.mul_comm (n+3) 2]
        ring
  have hs := Summable.of_nonneg_of_le (fun n => sq_nonneg _) hm
    hasSum_sine_coupling_majorant.summable
  refine ⟨hs, ?_⟩
  simpa only [hasSum_sine_coupling_majorant.tsum_eq] using
    hs.tsum_le_tsum hm hasSum_sine_coupling_majorant.summable

theorem sine_coupling_square_sum_bound :
    Summable (fun n : ℕ => (sineMatrixEntry thetaParameter nome 1 (n+2))^2) ∧
    (∑' n : ℕ, (sineMatrixEntry thetaParameter nome 1 (n+2))^2) < 3916 := by
  let b (n : ℕ) := (sineMatrixEntry thetaParameter nome 1 (n+2))^2
  have ht : Summable (fun n : ℕ => b (n+2)) ∧
      (∑' n : ℕ, b (n+2)) ≤ (sineCouplingTail:ℝ) := by
    simpa only [b, Nat.add_assoc] using sine_coupling_tail_bound
  have hs : Summable b := (summable_nat_add_iff 2).mp ht.1
  have hentry (k : ℕ) :
      (sineMatrixEntry thetaParameter nome 1 k)^2 ≤ (absUpper (sineEntry 1 k):ℝ)^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg _)
      (absUpper_sound _ _ (theta_nome_sine_matrix_enclosure 1 k)) 2
    simpa only [sq_abs] using h
  refine ⟨hs, ?_⟩
  calc
    _ = b 0+b 1+(∑' n : ℕ, b (n+2)) := by
      rw [← hs.sum_add_tsum_nat_add 2]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    _ ≤ (absUpper (sineEntry 1 2):ℝ)^2+
        (absUpper (sineEntry 1 3):ℝ)^2+(sineCouplingTail:ℝ) :=
      add_le_add (add_le_add (hentry 2) (hentry 3)) ht.2
    _ = (sineCouplingBound:ℝ) := by simp only [sineCouplingBound, Rat.cast_add, Rat.cast_pow]
    _ < 3916 := by exact_mod_cast sine_coupling_certificate

theorem sine_coupling_mem_l2 :
    Memℓp (fun n : ℕ => (sineMatrixEntry thetaParameter nome 1 (n+2):ℂ)) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mpr
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real,
    Real.norm_eq_abs, sq_abs] using sine_coupling_square_sum_bound.1

noncomputable def sineCouplingVector : SineTailSpace :=
  ⟨fun n => (sineMatrixEntry thetaParameter nome 1 (n+2):ℂ), sine_coupling_mem_l2⟩

theorem sine_coupling_norm_sq : ‖sineCouplingVector‖^2 =
    ∑' n : ℕ, (sineMatrixEntry thetaParameter nome 1 (n+2))^2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2:ℝ≥0∞).toReal) sineCouplingVector
  simpa [Real.rpow_two, Complex.norm_real, Real.norm_eq_abs, sq_abs, sineCouplingVector] using h

theorem sine_coupling_norm_bound : ‖sineCouplingVector‖ < 63 := by
  have h := sine_coupling_square_sum_bound.2
  rw [← sine_coupling_norm_sq] at h
  nlinarith [norm_nonneg sineCouplingVector]

theorem sine_coupling_pairing_bound (v : SineTailSpace) :
    ‖inner ℂ sineCouplingVector v‖ ≤ 63*‖v‖ :=
  (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right sine_coupling_norm_bound.le (norm_nonneg _))

end Lemniscate.CoarseArithmetic
