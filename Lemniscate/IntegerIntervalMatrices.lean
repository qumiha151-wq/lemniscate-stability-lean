import Lemniscate.IntegerIntervals
import Mathlib.Algebra.BigOperators.Field

/-! Real-matrix soundness of the common-denominator integer operations. -/
namespace Lemniscate.CoarseArithmetic
open Matrix

def integerMatrixInterval {ι κ : Type*} (I : Matrix ι κ IntegerInterval) :
    Matrix ι κ Interval := fun i j => (I i j).toInterval

def integerMatrixAdd {ι κ : Type*} (I J : Matrix ι κ IntegerInterval) :
    Matrix ι κ IntegerInterval := fun i j => integerAdd (I i j) (J i j)
def integerMatrixTranspose {ι κ : Type*} (I : Matrix ι κ IntegerInterval) :
    Matrix κ ι IntegerInterval := fun i j => I j i
def integerMatrixScale {ι κ : Type*} (c : IntegerInterval) (I : Matrix ι κ IntegerInterval) :
    Matrix ι κ IntegerInterval := fun i j => integerMul c (I i j)
def integerMatrixMul {ι κ μ : Type*} [Fintype κ]
    (I : Matrix ι κ IntegerInterval) (J : Matrix κ μ IntegerInterval) :
    Matrix ι μ IntegerInterval := fun i j =>
  ⟨∑ r, (integerMul (I i r) (J r j)).lo, ∑ r, (integerMul (I i r) (J r j)).hi⟩

theorem integer_matrix_enlargement {ι κ : Type*} (I J : Matrix ι κ IntegerInterval)
    (A : Matrix ι κ ℝ) (h : ∀ i j, IntegerEncloses (I i j) (J i j))
    (hJ : MatrixContains (integerMatrixInterval J) A) :
    MatrixContains (integerMatrixInterval I) A := by
  intro i j
  exact (hJ i j).mono (integer_encloses_sound _ _ (h i j)).1
    (integer_encloses_sound _ _ (h i j)).2

theorem integer_matrix_add_sound {ι κ : Type*} (I J : Matrix ι κ IntegerInterval)
    (A B : Matrix ι κ ℝ) (hI : MatrixContains (integerMatrixInterval I) A)
    (hJ : MatrixContains (integerMatrixInterval J) B) :
    MatrixContains (integerMatrixInterval (integerMatrixAdd I J)) (A+B) := by
  intro i j
  change Contains (integerAdd (I i j) (J i j)).toInterval (A i j+B i j)
  rw [integer_add_to_interval]
  exact add_sound _ _ _ _ (hI i j) (hJ i j)

theorem integer_matrix_transpose_sound {ι κ : Type*} (I : Matrix ι κ IntegerInterval)
    (A : Matrix ι κ ℝ) (hI : MatrixContains (integerMatrixInterval I) A) :
    MatrixContains (integerMatrixInterval (integerMatrixTranspose I)) Aᵀ := fun i j => hI j i

theorem integer_matrix_scale_sound {ι κ : Type*} (c : IntegerInterval) (x : ℝ)
    (I : Matrix ι κ IntegerInterval) (A : Matrix ι κ ℝ)
    (hc : Contains c.toInterval x) (hI : MatrixContains (integerMatrixInterval I) A) :
    MatrixContains (integerMatrixInterval (integerMatrixScale c I)) (x • A) := by
  intro i j
  exact integer_mul_sound _ _ _ _ hc (hI i j)

theorem integer_matrix_mul_sound {ι κ μ : Type*} [Fintype κ]
    (I : Matrix ι κ IntegerInterval) (J : Matrix κ μ IntegerInterval)
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ)
    (hI : MatrixContains (integerMatrixInterval I) A)
    (hJ : MatrixContains (integerMatrixInterval J) B) :
    MatrixContains (integerMatrixInterval (integerMatrixMul I J)) (A*B) := by
  intro i j
  have h := sum_interval_sound (fun r => (integerMul (I i r) (J r j)).toInterval)
    (fun r => A i r*B r j) (fun r => integer_mul_sound _ _ _ _ (hI i r) (hJ r j))
  simpa only [integerMatrixInterval, integerMatrixMul, IntegerInterval.toInterval,
    Int.cast_sum, Finset.sum_div, Matrix.mul_apply] using h

end Lemniscate.CoarseArithmetic
