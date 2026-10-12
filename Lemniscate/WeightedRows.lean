import Lemniscate.Algebra
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The weighted row argument on every finite set of indices.
There is no assumption that weights have a positive uniform lower bound.
The extension from Fourier polynomials to the Sobolev form domain is separate.
-/
namespace Lemniscate
open Finset

theorem weighted_pair_bound (s di dj x y : ℝ) (hi : 0 < di) (hj : 0 < dj) :
    2*(s*x*y) ≤ |s| * (dj/di*x^2+di/dj*y^2) := by
  have ht : 0 < di/dj := div_pos hi hj
  have hyoung := weighted_young |x| |y| (di/dj) ht
  have he : |x|^2/(di/dj)+(di/dj)*|y|^2 = dj/di*x^2+di/dj*y^2 := by
    rw [sq_abs, sq_abs]
    field_simp
  rw [he] at hyoung
  have hm := mul_le_mul_of_nonneg_left hyoung (abs_nonneg s)
  have hs : s*x*y ≤ |s| * (|x| * |y|) := by
    simpa [abs_mul, mul_assoc] using le_abs_self (s*x*y)
  nlinarith

theorem weighted_double_sum_bound {ι : Type*} (I : Finset ι)
    (S : ι → ι → ℝ) (d v : ι → ℝ)
    (hd : ∀ i ∈ I, 0 < d i) (hsym : ∀ i ∈ I, ∀ j ∈ I, S i j = S j i) :
    ∑ i ∈ I, ∑ j ∈ I, S i j*v i*v j ≤
      ∑ i ∈ I, (∑ j ∈ I, |S i j| * (d j/d i))*(v i)^2 := by
  have hp : 2*(∑ i ∈ I, ∑ j ∈ I, S i j*v i*v j) ≤
      ∑ i ∈ I, ∑ j ∈ I,
        |S i j| * (d j/d i*(v i)^2+d i/d j*(v j)^2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    exact weighted_pair_bound _ _ _ _ _ (hd i hi) (hd j hj)
  have hswap :
      (∑ i ∈ I, ∑ j ∈ I, |S i j| * (d i/d j)*(v j)^2) =
        ∑ i ∈ I, ∑ j ∈ I, |S i j| * (d j/d i)*(v i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsym j hj i hi]
  simp only [mul_add, Finset.sum_add_distrib] at hp
  simp only [← mul_assoc] at hp
  rw [hswap] at hp
  have hfactor :
      (∑ i ∈ I, ∑ j ∈ I, |S i j| * (d j/d i)*(v i)^2) =
      ∑ i ∈ I, (∑ j ∈ I, |S i j| * (d j/d i))*(v i)^2 := by
    simp only [Finset.sum_mul]
  rw [hfactor] at hp
  linarith

/-- Diagonal entries are kept with their signs; `off` denotes only the
off-diagonal matrix, and may be chosen to be zero on the diagonal. -/
theorem weighted_row_dissipation {ι : Type*} (I : Finset ι)
    (diagonal : ι → ℝ) (off : ι → ι → ℝ) (d v : ι → ℝ) (gap : ℝ)
    (hd : ∀ i ∈ I, 0 < d i)
    (hsym : ∀ i ∈ I, ∀ j ∈ I, off i j = off j i)
    (hrow : ∀ i ∈ I, diagonal i+∑ j ∈ I, |off i j| * (d j/d i) ≤ -gap) :
    (∑ i ∈ I, diagonal i*(v i)^2) +
      (∑ i ∈ I, ∑ j ∈ I, off i j*v i*v j) ≤
        -gap*(∑ i ∈ I, (v i)^2) := by
  have hoff := weighted_double_sum_bound I off d v hd hsym
  have hr : (∑ i ∈ I, diagonal i*(v i)^2) +
      (∑ i ∈ I, (∑ j ∈ I, |off i j| * (d j/d i))*(v i)^2) ≤
      -gap*(∑ i ∈ I, (v i)^2) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa [add_mul] using mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg (v i))
  linarith

end Lemniscate
