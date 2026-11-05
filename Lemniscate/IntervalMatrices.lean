import Lemniscate.RoundedIntervals
import Mathlib.Data.Matrix.Mul

/-! Real-matrix soundness of the rounded interval operations used in the
finite Bloch certificate. Every multiplication is rounded outwards. -/
namespace Lemniscate.CoarseArithmetic
open Matrix

def MatrixContains {ι κ : Type*} (I : Matrix ι κ Interval) (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, Contains (I i j) (A i j)

def intervalMatrixAdd {ι κ : Type*} (I J : Matrix ι κ Interval) : Matrix ι κ Interval :=
  fun i j => add (I i j) (J i j)

def intervalMatrixNeg {ι κ : Type*} (I : Matrix ι κ Interval) : Matrix ι κ Interval :=
  fun i j => scale (I i j) (-1)

def intervalMatrixTranspose {ι κ : Type*} (I : Matrix ι κ Interval) : Matrix κ ι Interval :=
  fun i j => I j i

def intervalMatrixScale {ι κ : Type*} (digits : ℕ) (c : Interval) (I : Matrix ι κ Interval) :
    Matrix ι κ Interval := fun i j => roundInterval digits (mul c (I i j))

def intervalMatrixMul {ι κ μ : Type*} [Fintype κ] (digits : ℕ)
    (I : Matrix ι κ Interval) (J : Matrix κ μ Interval) : Matrix ι μ Interval :=
  fun i j => ⟨∑ r, (roundInterval digits (mul (I i r) (J r j))).lo,
    ∑ r, (roundInterval digits (mul (I i r) (J r j))).hi⟩

theorem interval_matrix_add_sound {ι κ : Type*} (I J : Matrix ι κ Interval)
    (A B : Matrix ι κ ℝ) (hI : MatrixContains I A) (hJ : MatrixContains J B) :
    MatrixContains (intervalMatrixAdd I J) (A+B) := by
  intro i j
  exact add_sound _ _ _ _ (hI i j) (hJ i j)

theorem interval_matrix_neg_sound {ι κ : Type*} (I : Matrix ι κ Interval)
    (A : Matrix ι κ ℝ) (hI : MatrixContains I A) :
    MatrixContains (intervalMatrixNeg I) (-A) := by
  intro i j
  change Contains (scale (I i j) (-1)) (-(A i j))
  simpa only [Rat.cast_neg, Rat.cast_one, mul_neg_one] using scale_sound _ _ (-1) (hI i j)

theorem interval_matrix_transpose_sound {ι κ : Type*} (I : Matrix ι κ Interval)
    (A : Matrix ι κ ℝ) (hI : MatrixContains I A) :
    MatrixContains (intervalMatrixTranspose I) Aᵀ := by
  intro i j
  exact hI j i

theorem interval_matrix_scale_sound {ι κ : Type*} (digits : ℕ) (c : Interval) (x : ℝ)
    (I : Matrix ι κ Interval) (A : Matrix ι κ ℝ) (hc : Contains c x)
    (hI : MatrixContains I A) : MatrixContains (intervalMatrixScale digits c I) (x • A) := by
  intro i j
  exact roundInterval_sound _ _ _ (mul_sound _ _ _ _ hc (hI i j))

theorem interval_matrix_mul_sound {ι κ μ : Type*} [Fintype κ]
    (digits : ℕ) (I : Matrix ι κ Interval) (J : Matrix κ μ Interval)
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ)
    (hI : MatrixContains I A) (hJ : MatrixContains J B) :
    MatrixContains (intervalMatrixMul digits I J) (A*B) := by
  intro i j
  exact sum_interval_sound
    (fun r => roundInterval digits (mul (I i r) (J r j)))
    (fun r => A i r*B r j)
    (fun r => roundInterval_sound _ _ _ (mul_sound _ _ _ _ (hI i r) (hJ r j)))

end Lemniscate.CoarseArithmetic
