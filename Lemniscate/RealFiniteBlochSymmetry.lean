import Lemniscate.RealFiniteBlochMatrices

/-! Symmetry of the actual real Bernstein matrices, independent of their
rational interval enclosures. -/
namespace Lemniscate
open Matrix

theorem real_head_hermitian_part_transpose (A : Matrix (Fin 31) (Fin 31) ℝ) :
    (realHeadHermitianPart A)ᵀ = realHeadHermitianPart A := by
  simp only [realHeadHermitianPart, transpose_smul, transpose_add, transpose_transpose]
  rw [add_comm Aᵀ A]

theorem real_finite_symmetric_head_transpose (r q : ℝ) (j : Fin 5) :
    (realFiniteSymmetricHead r q j)ᵀ = realFiniteSymmetricHead r q j :=
  real_head_hermitian_part_transpose _

theorem real_finite_bloch_coefficient_transpose (r q : ℝ) (j : Fin 5) :
    (realFiniteBlochCoefficient r q j)ᵀ = realFiniteBlochCoefficient r q j := by
  fin_cases j <;>
    norm_num [realFiniteBlochCoefficient, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons,
      transpose_add, transpose_mul, transpose_smul, transpose_transpose,
      real_finite_symmetric_head_transpose, mul_assoc] <;> abel

theorem real_finite_bloch_bernstein_transpose (r q : ℝ) (k : Fin 5) :
    (realFiniteBlochBernstein r q k)ᵀ = realFiniteBlochBernstein r q k := by
  fin_cases k <;>
    norm_num [realFiniteBlochBernstein, realQuarticMatrixBernstein,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, transpose_add, transpose_smul,
      real_finite_bloch_coefficient_transpose]

theorem real_finite_bloch_bernstein_symm (r q : ℝ) (k : Fin 5) (i j : Fin 31) :
    realFiniteBlochBernstein r q k i j = realFiniteBlochBernstein r q k j i :=
  (congrArg (fun M : Matrix (Fin 31) (Fin 31) ℝ => M i j)
    (real_finite_bloch_bernstein_transpose r q k)).symm

end Lemniscate
