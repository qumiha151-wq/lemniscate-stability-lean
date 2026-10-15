import Lemniscate.CosineHighRows
import Lemniscate.ComplexRows

/-! Dissipation of the actual coefficient-defined cosine matrix on every
finite set of complex modes. Extension to the Sobolev form domain remains
separate; no inverse boundedness of the decaying weights is assumed. -/
namespace Lemniscate.CoarseArithmetic
open Finset Complex
open scoped ComplexConjugate

noncomputable def cosineOffMatrix (j k : ℕ) : ℂ :=
  if j = k then 0 else (cosineMatrixEntry thetaParameter nome j k:ℂ)

theorem cosine_off_row_nonneg (j k : ℕ) : 0 ≤ cosineOffRow j k := by
  have hj : (0:ℝ) < (weight j:ℝ) := by exact_mod_cast weight_pos j
  have hk : (0:ℝ) < (weight k:ℝ) := by exact_mod_cast weight_pos k
  by_cases h : k = j
  · simp [cosineOffRow, h]
  · simp only [cosineOffRow, if_neg h]
    exact mul_nonneg (abs_nonneg _) (le_of_lt (div_pos hk hj))

theorem cosine_finite_row_bound (I : Finset ℕ) (j : ℕ) :
    cosineMatrixEntry thetaParameter nome j j + ∑ k ∈ I, cosineOffRow j k ≤ -(21/4:ℝ) := by
  have h := cosine_all_rows_dissipative j
  have hf := Summable.sum_le_tsum I (fun k _ => cosine_off_row_nonneg j k) h.1
  exact (add_le_add le_rfl hf).trans h.2.le

theorem cosine_off_norm_weight (j k : ℕ) :
    ‖cosineOffMatrix j k‖*((weight k:ℝ)/(weight j:ℝ)) = cosineOffRow j k := by
  by_cases h : k = j
  · subst k
    simp [cosineOffMatrix, cosineOffRow]
  · simp [cosineOffMatrix, cosineOffRow, h, Ne.symm h, Complex.norm_real, Real.norm_eq_abs]

theorem cosine_off_norm_symmetric (j k : ℕ) :
    ‖cosineOffMatrix j k‖ = ‖cosineOffMatrix k j‖ := by
  by_cases h : j = k
  · subst k
    rfl
  · simp only [cosineOffMatrix, if_neg h, if_neg (Ne.symm h)]
    rw [cosine_matrix_symmetric thetaParameter nome j k]

theorem cosine_finite_split_dissipative (I : Finset ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ I, cosineMatrixEntry thetaParameter nome i i*‖v i‖^2) +
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*cosineOffMatrix i j*v j).re ≤
        -(21/4:ℝ)*(∑ i ∈ I, ‖v i‖^2) := by
  apply complex_weighted_row_dissipation I _ cosineOffMatrix (fun i => (weight i:ℝ)) v (21/4)
  · intro i _
    exact_mod_cast weight_pos i
  · intro i _ j _
    exact cosine_off_norm_symmetric i j
  · intro i _
    simp_rw [cosine_off_norm_weight]
    exact cosine_finite_row_bound I i

theorem cosine_finite_form_dissipative (I : Finset ℕ) (v : ℕ → ℂ) :
    (∑ i ∈ I, ∑ j ∈ I,
      conj (v i)*(cosineMatrixEntry thetaParameter nome i j:ℂ)*v j).re ≤
        -(21/4:ℝ)*(∑ i ∈ I, ‖v i‖^2) := by
  have hd (i : ℕ) : conj (v i)*(cosineMatrixEntry thetaParameter nome i i:ℂ)*v i =
      ((cosineMatrixEntry thetaParameter nome i i*‖v i‖^2:ℝ):ℂ) := by
    calc
      _ = (cosineMatrixEntry thetaParameter nome i i:ℂ)*(conj (v i)*v i) := by ring
      _ = _ := by rw [Complex.conj_mul']; simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have he (i j : ℕ) : conj (v i)*(cosineMatrixEntry thetaParameter nome i j:ℂ)*v j =
      (if j = i then ((cosineMatrixEntry thetaParameter nome i i*‖v i‖^2:ℝ):ℂ) else 0)+
      conj (v i)*cosineOffMatrix i j*v j := by
    by_cases h : j = i
    · subst j
      simpa only [cosineOffMatrix, if_pos rfl, ite_true, mul_zero, zero_mul, add_zero] using hd i
    · simp [cosineOffMatrix, h, Ne.symm h]
  have hsplit :
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*(cosineMatrixEntry thetaParameter nome i j:ℂ)*v j) =
      (∑ i ∈ I, ((cosineMatrixEntry thetaParameter nome i i*‖v i‖^2:ℝ):ℂ))+
      (∑ i ∈ I, ∑ j ∈ I, conj (v i)*cosineOffMatrix i j*v j) := by
    simp_rw [he, sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    simp [hi]
  rw [hsplit]
  simpa only [Complex.add_re, ← Complex.ofReal_sum, Complex.ofReal_re] using
    cosine_finite_split_dissipative I v

end Lemniscate.CoarseArithmetic
