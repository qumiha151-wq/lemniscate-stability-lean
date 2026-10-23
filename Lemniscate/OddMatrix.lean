import Lemniscate.OddRowSemantics

/-! The real two-sided odd-frequency matrix. Its finite low-row estimates are
deduced from the certified row polynomials; omitted tails are still explicit.
The parameter alpha is retained throughout the whole half interval. -/
namespace Lemniscate.OddArithmetic
open Finset CoarseArithmetic

noncomputable def oddMatrixEntry (α : ℝ) (n m : ℤ) : ℝ :=
  if n = m then -4*thetaParameter^2*((n:ℝ)+α)^4+
    45*thetaParameter*fourierCoefficient thetaParameter nome 0*((n:ℝ)+α)^2-42
  else thetaParameter*fourierCoefficient thetaParameter nome ((n-m).natAbs/2)*
    oddEntryPolynomial n m α

noncomputable def oddActualHead (n : ℤ) (α : ℝ) : ℝ :=
  ∑ m ∈ oddIndices.toFinset, if m = n then 0 else |oddMatrixEntry α n m| * oddWeight m α

theorem odd_matrix_symmetric (α : ℝ) (n m : ℤ) :
    oddMatrixEntry α n m = oddMatrixEntry α m n := by
  by_cases he : n = m
  · subst m
    rfl
  · have hd : (n-m).natAbs = (m-n).natAbs := by
      have h := congrArg Int.natAbs (show n-m = -(m-n) by omega)
      simpa only [Int.natAbs_neg] using h
    simp only [oddMatrixEntry, if_neg he, if_neg (Ne.symm he), hd, oddEntryPolynomial]
    ring

theorem odd_actual_head_le (n : ℤ) (hn : Odd n) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) : oddActualHead n α ≤ oddHeadMajorant n α := by
  have hb := odd_head_majorizes_coefficients n hn α hα hα'
  have he : oddActualHead n α =
      ∑ m ∈ oddIndices.toFinset, if m = n then 0 else
        |thetaParameter*fourierCoefficient thetaParameter nome ((n-m).natAbs/2)*
          oddEntryPolynomial n m α| * oddWeight m α := by
    unfold oddActualHead
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : m = n
    · simp [hm]
    · simp only [if_neg hm, oddMatrixEntry, if_neg (Ne.symm hm)]
  rw [he]
  exact hb

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem odd_constant_coefficient_lower_pos : (0:ℚ) < hLower 0 := by decide +kernel

theorem odd_matrix_diagonal_bound (α : ℝ) (n : ℤ) :
    oddMatrixEntry α n n ≤
      -4*(rlo:ℝ)^2*((n:ℝ)+α)^4+45*(rhi:ℝ)*(hUpper 0:ℝ)*((n:ℝ)+α)^2-42 := by
  have hh := theta_nome_fourier_enclosure 0
  have hc : 0 ≤ fourierCoefficient thetaParameter nome 0 :=
    (le_of_lt (show (0:ℝ) < (hLower 0:ℝ) by exact_mod_cast odd_constant_coefficient_lower_pos)).trans hh.1
  have hr := actual_nome_theta_r_bounds
  have hr0 : 0 ≤ (rlo:ℝ) := by norm_num [rlo]
  have hrlow : (rlo:ℝ) ≤ thetaParameter := hr.1
  have hr2 : (rlo:ℝ)^2 ≤ thetaParameter^2 := by nlinarith [hrlow]
  have hp : thetaParameter*fourierCoefficient thetaParameter nome 0 ≤ (rhi:ℝ)*(hUpper 0:ℝ) :=
    mul_le_mul hr.2 hh.2 hc (by norm_num [rhi])
  have hb4 := mul_le_mul_of_nonneg_right hr2 (by positivity : 0 ≤ ((n:ℝ)+α)^4)
  have hb2 := mul_le_mul_of_nonneg_right hp (sq_nonneg ((n:ℝ)+α))
  simp only [oddMatrixEntry, ite_true]
  nlinarith

theorem lowIndex_odd (i : Fin 12) : Odd (lowIndex i) := by
  refine ⟨(i.val:ℤ)-6, ?_⟩
  unfold lowIndex
  ring

theorem odd_low_row_with_omitted_bound (i : Fin 12) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    oddMatrixEntry α (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) α+
      oddActualHead (lowIndex i) α+(omitted (lowIndex i):ℝ) ≤
        -oddWeight (lowIndex i) α-1/2 := by
  have hf := odd_low_row_formula_positive i α hα hα'
  have hd := mul_le_mul_of_nonneg_right (odd_matrix_diagonal_bound α (lowIndex i))
    (le_of_lt (odd_weight_positive (lowIndex i) α hα hα'))
  have hh := odd_actual_head_le (lowIndex i) (lowIndex_odd i) α hα hα'
  nlinarith

theorem odd_zero_row_with_omitted_bound (i : Fin 12) :
    oddMatrixEntry 0 (lowIndex i) (lowIndex i)*oddWeight (lowIndex i) 0+
      oddActualHead (lowIndex i) 0+(omitted (lowIndex i):ℝ) <
        -6*oddWeight (lowIndex i) 0 := by
  have hf := odd_zero_weighted_low_margin i
  rw [odd_row_realEval_formula] at hf
  have hd := mul_le_mul_of_nonneg_right (odd_matrix_diagonal_bound 0 (lowIndex i))
    (le_of_lt (odd_weight_positive (lowIndex i) 0 (by norm_num) (by norm_num)))
  have hh := odd_actual_head_le (lowIndex i) (lowIndex_odd i) 0 (by norm_num) (by norm_num)
  nlinarith

end Lemniscate.OddArithmetic
