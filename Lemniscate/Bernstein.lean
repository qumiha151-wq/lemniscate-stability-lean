import Lemniscate.Algebra
import Mathlib.RingTheory.Polynomial.Bernstein

/-! Bernstein positivity and the exact degree-six conversion on [0, 1/2]. -/
namespace Lemniscate
open Finset

noncomputable def bernsteinBasis (n k : ℕ) (a : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n k).eval (2*a)

theorem bernsteinBasis_nonneg (n k : ℕ) (a : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    0 ≤ bernsteinBasis n k a := by
  have htwo : 0 ≤ 2*a := by linarith
  have hone : 0 ≤ 1-2*a := by linarith
  simp only [bernsteinBasis, bernsteinPolynomial, Polynomial.eval_mul,
    Polynomial.eval_natCast, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_one]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg htwo _))
    (pow_nonneg hone _)

theorem bernsteinBasis_sum (n : ℕ) (a : ℝ) :
    (∑ k ∈ range (n+1), bernsteinBasis n k a) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval (2*a)) (bernsteinPolynomial.sum ℝ n)
  simpa [bernsteinBasis, Polynomial.eval_finsetSum] using h

theorem bernstein_lower_bound (n : ℕ) (c : ℕ → ℝ) (a δ : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (hc : ∀ k ∈ range (n+1), δ ≤ c k) :
    δ ≤ ∑ k ∈ range (n+1), c k*bernsteinBasis n k a := by
  calc
    δ = ∑ k ∈ range (n+1), δ*bernsteinBasis n k a := by
      rw [← Finset.mul_sum, bernsteinBasis_sum, mul_one]
    _ ≤ _ := Finset.sum_le_sum fun k hk =>
      mul_le_mul_of_nonneg_right (hc k hk) (bernsteinBasis_nonneg n k a ha ha')

theorem bernstein_absolute_majorant (n : ℕ) (c : ℕ → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) :
    |∑ k ∈ range (n+1), c k*bernsteinBasis n k a| ≤
      ∑ k ∈ range (n+1), |c k| * bernsteinBasis n k a := by
  calc
    _ ≤ ∑ k ∈ range (n+1), |c k*bernsteinBasis n k a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_congr rfl fun k _ => by
      rw [abs_mul, abs_of_nonneg (bernsteinBasis_nonneg n k a ha ha')]

noncomputable def bernsteinCoefficient (n k : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ j ∈ range (k+1), ((k.choose j : ℝ)/(2^j*(n.choose j : ℝ)))*c j

theorem degree_six_conversion (c : ℕ → ℝ) (a : ℝ) :
    (∑ j ∈ range 7, c j*a^j) =
      ∑ k ∈ range 7, bernsteinCoefficient 6 k c*bernsteinBasis 6 k a := by
  norm_num [bernsteinCoefficient, bernsteinBasis, bernsteinPolynomial,
    Finset.sum_range_succ, Nat.choose]
  <;> ring

theorem degree_four_conversion (c : ℕ → ℝ) (a : ℝ) :
    (∑ j ∈ range 5, c j*a^j) =
      ∑ k ∈ range 5, bernsteinCoefficient 4 k c*bernsteinBasis 4 k a := by
  norm_num [bernsteinCoefficient, bernsteinBasis, bernsteinPolynomial,
    Finset.sum_range_succ, Nat.choose]
  <;> ring

theorem degree_six_polynomial_lower_bound (c : ℕ → ℝ) (a δ : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2)
    (hc : ∀ k ∈ range 7, δ ≤ bernsteinCoefficient 6 k c) :
    δ ≤ ∑ j ∈ range 7, c j*a^j := by
  rw [degree_six_conversion]
  exact bernstein_lower_bound 6 (fun k => bernsteinCoefficient 6 k c) a δ ha ha' hc

end Lemniscate
