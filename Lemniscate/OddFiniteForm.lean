import Lemniscate.OddAllRows
import Lemniscate.ComplexRows

/-! The complete odd matrix dissipates every finite complex coefficient vector.
The decaying row weights need no bounded inverse. Sobolev extension and the
nonzero-parameter differential-operator interpretation are separate obligations. -/
namespace Lemniscate.OddArithmetic
open Finset Complex
open scoped ComplexConjugate

noncomputable def oddIndexedMatrix (α : ℝ) (i j : ℤ) : ℝ :=
  oddMatrixEntry α (2*i+1) (2*j+1)

noncomputable def oddIndexedOffMatrix (α : ℝ) (i j : ℤ) : ℂ :=
  if i = j then 0 else (oddIndexedMatrix α i j:ℂ)

noncomputable def oddIndexedOffRow (α : ℝ) (i j : ℤ) : ℝ :=
  oddOffIndexRow α (2*i+1) j/oddWeight (2*i+1) α

theorem odd_indexed_row_nonneg (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) (i j : ℤ) :
    0 ≤ oddIndexedOffRow α i j := by
  unfold oddIndexedOffRow oddOffIndexRow oddWeightedOffEntry
  split_ifs
  · simp
  · exact div_nonneg (mul_nonneg (abs_nonneg _) (le_of_lt (odd_weight_positive _ α hα hα')))
      (le_of_lt (odd_weight_positive _ α hα hα'))

theorem odd_indexed_off_norm_weight (α : ℝ) (i j : ℤ) :
    ‖oddIndexedOffMatrix α i j‖*(oddWeight (2*j+1) α/oddWeight (2*i+1) α) =
      oddIndexedOffRow α i j := by
  by_cases he : i = j
  · subst j
    simp [oddIndexedOffMatrix, oddIndexedOffRow, oddOffIndexRow, oddWeightedOffEntry]
  · have hf : 2*j+1 ≠ 2*i+1 := by omega
    simp only [oddIndexedOffMatrix, if_neg he, Complex.norm_real, Real.norm_eq_abs,
      oddIndexedOffRow, oddOffIndexRow, oddWeightedOffEntry, if_neg hf, oddIndexedMatrix,
      mul_div_assoc]

theorem odd_indexed_off_norm_symmetric (α : ℝ) (i j : ℤ) :
    ‖oddIndexedOffMatrix α i j‖ = ‖oddIndexedOffMatrix α j i‖ := by
  by_cases he : i = j
  · subst j
    rfl
  · simp only [oddIndexedOffMatrix, if_neg he, if_neg (Ne.symm he), oddIndexedMatrix]
    rw [odd_matrix_symmetric α (2*i+1) (2*j+1)]

theorem odd_indexed_finite_row_bound (I : Finset ℤ) (i : ℤ) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) (gap : ℝ)
    (hrow : oddIndexedMatrix α i i+
      (∑' k : ℤ, oddOffIndexRow α (2*i+1) k)/oddWeight (2*i+1) α ≤ -gap) :
    oddIndexedMatrix α i i+∑ k ∈ I, oddIndexedOffRow α i k ≤ -gap := by
  have hs := (odd_all_rows_dissipative (2*i+1) ⟨i, rfl⟩ α hα hα').1
  have hn : Summable (oddIndexedOffRow α i) := hs.div_const _
  have hf := Summable.sum_le_tsum I (fun k _ => odd_indexed_row_nonneg α hα hα' i k) hn
  have he : (∑' k : ℤ, oddIndexedOffRow α i k) =
      (∑' k : ℤ, oddOffIndexRow α (2*i+1) k)/oddWeight (2*i+1) α := by
    simp only [oddIndexedOffRow, tsum_div_const]
  rw [he] at hf
  exact (add_le_add le_rfl hf).trans hrow

theorem odd_finite_form_of_row_bound (I : Finset ℤ) (v : ℤ → ℂ) (α gap : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2)
    (hrow : ∀ i : ℤ, oddIndexedMatrix α i i+
      (∑' k : ℤ, oddOffIndexRow α (2*i+1) k)/oddWeight (2*i+1) α ≤ -gap) :
    (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(oddIndexedMatrix α i j:ℂ)*v j).re ≤
      -gap*(∑ i ∈ I, ‖v i‖^2) := by
  have hsplit : (∑ i ∈ I, oddIndexedMatrix α i i*‖v i‖^2)+
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*oddIndexedOffMatrix α i j*v j).re ≤
        -gap*(∑ i ∈ I, ‖v i‖^2) := by
    apply complex_weighted_row_dissipation I _ (oddIndexedOffMatrix α)
      (fun i => oddWeight (2*i+1) α) v gap
    · intro i _
      exact odd_weight_positive _ α hα hα'
    · intro i _ j _
      exact odd_indexed_off_norm_symmetric α i j
    · intro i _
      simp_rw [odd_indexed_off_norm_weight]
      exact odd_indexed_finite_row_bound I i α hα hα' gap (hrow i)
  have hd (i : ℤ) : conj (v i)*(oddIndexedMatrix α i i:ℂ)*v i =
      ((oddIndexedMatrix α i i*‖v i‖^2:ℝ):ℂ) := by
    calc
      _ = (oddIndexedMatrix α i i:ℂ)*(conj (v i)*v i) := by ring
      _ = _ := by rw [Complex.conj_mul']; simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have he (i j : ℤ) : conj (v i)*(oddIndexedMatrix α i j:ℂ)*v j =
      (if j = i then ((oddIndexedMatrix α i i*‖v i‖^2:ℝ):ℂ) else 0)+
      conj (v i)*oddIndexedOffMatrix α i j*v j := by
    by_cases hij : j = i
    · subst j
      simpa only [oddIndexedOffMatrix, ite_true, mul_zero, zero_mul, add_zero] using hd i
    · simp [oddIndexedOffMatrix, hij, Ne.symm hij]
  have hsum : (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(oddIndexedMatrix α i j:ℂ)*v j) =
      (∑ i ∈ I, ((oddIndexedMatrix α i i*‖v i‖^2:ℝ):ℂ))+
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*oddIndexedOffMatrix α i j*v j) := by
    simp_rw [he, sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp [hi]
  rw [hsum]
  simpa only [Complex.add_re, ← Complex.ofReal_sum, Complex.ofReal_re] using hsplit

theorem odd_finite_form_dissipative (I : Finset ℤ) (v : ℤ → ℂ) (α : ℝ)
    (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(oddIndexedMatrix α i j:ℂ)*v j).re ≤
      -(∑ i ∈ I, ‖v i‖^2) := by
  simpa only [neg_mul, one_mul] using odd_finite_form_of_row_bound I v α 1 hα hα'
    (fun i => (odd_all_rows_dissipative (2*i+1) ⟨i, rfl⟩ α hα hα').2.le)

theorem odd_zero_finite_form_dissipative (I : Finset ℤ) (v : ℤ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(oddIndexedMatrix 0 i j:ℂ)*v j).re ≤
      -6*(∑ i ∈ I, ‖v i‖^2) :=
  odd_finite_form_of_row_bound I v 0 6 (by norm_num) (by norm_num)
    (fun i => (odd_zero_all_rows_dissipative (2*i+1) ⟨i, rfl⟩).2.le)

end Lemniscate.OddArithmetic
