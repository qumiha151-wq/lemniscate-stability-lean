import Lemniscate.OddWeights
import Lemniscate.OddEntryPolynomials

/-! The real meaning of the computed odd-row polynomial, including its entire
finite head. The omitted-column expression is kept explicit; proving that it
bounds the infinite omitted sum is a subsequent analytic obligation. -/
namespace Lemniscate.OddArithmetic
open Finset CoarseArithmetic

noncomputable def oddHeadMajorant (n : ℤ) (α : ℝ) : ℝ :=
  ∑ m ∈ oddIndices.toFinset, if m = n then 0 else
    realEval (absoluteEntryPolynomial n m) α*oddWeight m α

theorem odd_indices_nodup : oddIndices.Nodup := by decide +kernel

theorem odd_indices_odd (m : ℤ) (hm : m ∈ oddIndices.toFinset) : Odd m := by
  have hl := List.mem_toFinset.mp hm
  rcases List.mem_map.mp hl with ⟨j, _, rfl⟩
  refine ⟨(j:ℤ)-13, ?_⟩
  ring

theorem realEval_odd_fold (n : ℤ) (α : ℝ) (l : List ℤ) (p : Poly) :
    realEval (l.foldl (fun q m => if m = n then q else
      polyAdd q (polyScale (polyMul (absoluteEntryPolynomial n m) (weight m)) (-1))) p) α =
      realEval p α-(l.map (fun m => if m = n then 0 else
        realEval (absoluteEntryPolynomial n m) α*oddWeight m α)).sum := by
  induction l generalizing p with
  | nil => simp
  | cons m l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    by_cases hm : m = n
    · simp [hm]
    · simp only [if_neg hm, realEval_add, realEval_scale, realEval_mul,
        Rat.cast_neg, Rat.cast_one, neg_one_mul, oddWeight]
      ring

theorem odd_row_realEval_formula (n : ℤ) (α : ℝ) :
    realEval (rowPolynomial n) α =
      (4*(rlo:ℝ)^2*((n:ℝ)+α)^4-45*(rhi:ℝ)*(hUpper 0:ℝ)*((n:ℝ)+α)^2+41)*
        oddWeight n α - oddHeadMajorant n α - (omitted n:ℝ) := by
  have hlinear : realEval [(n:ℚ),1] α = (n:ℝ)+α := by
    simp [realEval_eq_sum, coeff, Finset.sum_range_succ]
  unfold rowPolynomial
  rw [realEval_add, realEval_odd_fold]
  simp only [realEval_mul, realEval_add, realEval_scale, realEval_const, hlinear,
    Rat.cast_neg, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  rw [← List.sum_toFinset _ odd_indices_nodup]
  change _ = _*realEval (weight n) α - oddHeadMajorant n α - (omitted n:ℝ)
  unfold oddHeadMajorant oddWeight
  ring

theorem odd_low_row_formula_positive (i : Fin 12) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (1/2:ℝ) ≤
      (4*(rlo:ℝ)^2*((lowIndex i:ℝ)+α)^4-
        45*(rhi:ℝ)*(hUpper 0:ℝ)*((lowIndex i:ℝ)+α)^2+41)*
        oddWeight (lowIndex i) α - oddHeadMajorant (lowIndex i) α - (omitted (lowIndex i):ℝ) := by
  rw [← odd_row_realEval_formula]
  exact odd_low_realEval_positive i α hα hα'

theorem odd_head_majorizes_coefficients (n : ℤ) (hn : Odd n) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑ m ∈ oddIndices.toFinset, if m = n then 0 else
      |thetaParameter*fourierCoefficient thetaParameter nome ((n-m).natAbs/2)*
        oddEntryPolynomial n m α| * oddWeight m α) ≤ oddHeadMajorant n α := by
  unfold oddHeadMajorant
  apply Finset.sum_le_sum
  intro m hm
  by_cases he : m = n
  · simp [he]
  · simp only [if_neg he]
    exact mul_le_mul_of_nonneg_right
      (theta_nome_odd_off_diagonal_bound n m hn (odd_indices_odd m hm) (Ne.symm he) α hα hα')
      (le_of_lt (odd_weight_positive m α hα hα'))

end Lemniscate.OddArithmetic
