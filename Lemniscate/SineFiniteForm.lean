import Lemniscate.SineRows
import Lemniscate.ComplexRows

/-! The sine tail block is dissipative on every finite set of complex modes,
with the paper's bound -100. Index i here represents sine frequency 2(i+2). -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex
open scoped ComplexConjugate

noncomputable def sineTailOffMatrix (i j : ℕ) : ℂ :=
  if i = j then 0 else (sineMatrixEntry thetaParameter nome (i+2) (j+2):ℂ)

theorem sine_tail_finite_row_bound (I : Finset ℕ) (i : ℕ) :
    sineMatrixEntry thetaParameter nome (i+2) (i+2) +
      (∑ j ∈ I, sineOffRow (i+2) (j+2)) ≤ -100 := by
  have h := sine_all_tail_rows_dissipative (i+2) (by omega)
  have hs : Summable (fun j : ℕ => sineOffRow (i+2) (j+2)) :=
    (summable_nat_add_iff 2).mpr h.1
  have hz : (∑ k ∈ range 2, sineOffRow (i+2) k) = 0 := by
    simp [sum_range_succ, sineOffRow]
  have he : (∑' j : ℕ, sineOffRow (i+2) (j+2)) = ∑' j : ℕ, sineOffRow (i+2) j := by
    have hh := h.1.sum_add_tsum_nat_add 2
    simpa only [hz, zero_add] using hh
  have hf := Summable.sum_le_tsum I (fun j _ => sine_off_row_nonneg (i+2) (j+2)) hs
  rw [he] at hf
  exact (add_le_add le_rfl hf).trans h.2.le

theorem sine_tail_off_norm (i j : ℕ) :
    ‖sineTailOffMatrix i j‖ = sineOffRow (i+2) (j+2) := by
  by_cases h : i = j
  · subst j
    simp [sineTailOffMatrix, sineOffRow]
  · simp [sineTailOffMatrix, sineOffRow, h, Ne.symm h,
      show ¬j+2 < 2 by omega, Complex.norm_real, Real.norm_eq_abs]

theorem sine_tail_off_norm_symmetric (i j : ℕ) :
    ‖sineTailOffMatrix i j‖ = ‖sineTailOffMatrix j i‖ := by
  by_cases h : i = j
  · subst j; rfl
  · simp only [sineTailOffMatrix, if_neg h, if_neg (Ne.symm h)]
    rw [sine_matrix_symmetric thetaParameter nome (i+2) (j+2)]

theorem sine_tail_finite_split_dissipative (I : Finset ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ I, sineMatrixEntry thetaParameter nome (i+2) (i+2)*‖v i‖^2) +
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*sineTailOffMatrix i j*v j).re ≤
        -100*(∑ i ∈ I, ‖v i‖^2) := by
  apply complex_weighted_row_dissipation I _ sineTailOffMatrix (fun _ => 1) v 100
  · intro i _; norm_num
  · intro i _ j _
    exact sine_tail_off_norm_symmetric i j
  · intro i _
    simpa only [div_self (by norm_num : (1:ℝ) ≠ 0), mul_one, sine_tail_off_norm] using
      sine_tail_finite_row_bound I i

theorem sine_tail_finite_form_dissipative (I : Finset ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ I,
      conj (v i)*(sineMatrixEntry thetaParameter nome (i+2) (j+2):ℂ)*v j).re ≤
        -100*(∑ i ∈ I, ‖v i‖^2) := by
  have hd (i : ℕ) :
      conj (v i)*(sineMatrixEntry thetaParameter nome (i+2) (i+2):ℂ)*v i =
      ((sineMatrixEntry thetaParameter nome (i+2) (i+2)*‖v i‖^2:ℝ):ℂ) := by
    calc
      _ = (sineMatrixEntry thetaParameter nome (i+2) (i+2):ℂ)*(conj (v i)*v i) := by ring
      _ = _ := by rw [Complex.conj_mul']; simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have he (i j : ℕ) :
      conj (v i)*(sineMatrixEntry thetaParameter nome (i+2) (j+2):ℂ)*v j =
      (if j = i then ((sineMatrixEntry thetaParameter nome (i+2) (i+2)*‖v i‖^2:ℝ):ℂ) else 0)+
        conj (v i)*sineTailOffMatrix i j*v j := by
    by_cases h : j = i
    · subst j
      simpa only [sineTailOffMatrix, if_pos rfl, ite_true, mul_zero, zero_mul, add_zero] using hd i
    · simp [sineTailOffMatrix, h, Ne.symm h]
  have hsplit :
      (∑ i ∈ I, ∑ j ∈ I,
        conj (v i)*(sineMatrixEntry thetaParameter nome (i+2) (j+2):ℂ)*v j) =
      (∑ i ∈ I, ((sineMatrixEntry thetaParameter nome (i+2) (i+2)*‖v i‖^2:ℝ):ℂ))+
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*sineTailOffMatrix i j*v j) := by
    simp_rw [he, sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp [hi]
  rw [hsplit]
  simpa only [Complex.add_re, ← Complex.ofReal_sum, Complex.ofReal_re] using
    sine_tail_finite_split_dissipative I v

end Lemniscate.CoarseArithmetic
