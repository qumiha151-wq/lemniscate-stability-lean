import Lemniscate.OddPositivity

/-! Semantics of the rational coefficient lists used by the odd-row certificates.
Addition, scaling and truncated convolution are identified with genuine
polynomial operations before their real evaluations are used in estimates. -/
namespace Lemniscate.OddArithmetic
open Finset CoarseArithmetic

theorem coeff_eq_zero_of_length_le (p : Poly) (n : ℕ) (hn : p.length ≤ n) : coeff p n = 0 := by
  simp [coeff, List.getElem?_eq_none hn]

theorem coeff_polyAdd (p q : Poly) (n : ℕ) :
    coeff (polyAdd p q) n = coeff p n+coeff q n := by
  by_cases hn : n < max p.length q.length
  · simp [polyAdd, coeff, hn]
  · have hp : p.length ≤ n := by omega
    have hq : q.length ≤ n := by omega
    rw [coeff_eq_zero_of_length_le p n hp, coeff_eq_zero_of_length_le q n hq]
    simpa only [add_zero] using coeff_eq_zero_of_length_le (polyAdd p q) n (by
      simp only [polyAdd, List.length_map, List.length_range]
      omega)

theorem coeff_polyScale (p : Poly) (t : ℚ) (n : ℕ) :
    coeff (polyScale p t) n = t*coeff p n := by
  simp only [coeff, polyScale, List.getElem?_map]
  simpa only [mul_zero] using Option.getD_map (fun x : ℚ => t*x) 0 p[n]?

theorem coeff_polyMul (p q : Poly) (n : ℕ) :
    coeff (polyMul p q) n = ∑ k ∈ range (n+1), coeff p k*coeff q (n-k) := by
  by_cases hn : n < p.length+q.length-1
  · simp [polyMul, coeff, hn, sumTo_eq_sum_range]
  · rw [coeff_eq_zero_of_length_le (polyMul p q) n (by
      simp only [polyMul, List.length_map, List.length_range]
      omega)]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
    by_cases hp : p.length ≤ k
    · rw [coeff_eq_zero_of_length_le p k hp, zero_mul]
    · rw [coeff_eq_zero_of_length_le q (n-k) (by omega), mul_zero]

noncomputable def polyAsPolynomial (p : Poly) : Polynomial ℚ :=
  ∑ n ∈ range p.length, Polynomial.monomial n (coeff p n)

theorem polyAsPolynomial_coeff (p : Poly) (n : ℕ) :
    (polyAsPolynomial p).coeff n = coeff p n := by
  simp only [polyAsPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n < p.length
  · simp [hn]
  · simp [hn, coeff_eq_zero_of_length_le p n (by omega)]

theorem polyAsPolynomial_add (p q : Poly) :
    polyAsPolynomial (polyAdd p q) = polyAsPolynomial p+polyAsPolynomial q := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_add, polyAsPolynomial_coeff, coeff_polyAdd]

theorem polyAsPolynomial_scale (p : Poly) (t : ℚ) :
    polyAsPolynomial (polyScale p t) = Polynomial.C t*polyAsPolynomial p := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_C_mul, polyAsPolynomial_coeff, coeff_polyScale]

theorem polyAsPolynomial_mul (p q : Poly) :
    polyAsPolynomial (polyMul p q) = polyAsPolynomial p*polyAsPolynomial q := by
  apply Polynomial.ext
  intro n
  simp only [Polynomial.coeff_mul, polyAsPolynomial_coeff, coeff_polyMul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

noncomputable def realEval (p : Poly) (α : ℝ) : ℝ :=
  (polyAsPolynomial p).eval₂ (Rat.castHom ℝ) α

theorem realEval_eq_sum (p : Poly) (α : ℝ) :
    realEval p α = ∑ j ∈ range p.length, (coeff p j : ℝ)*α^j := by
  simp only [realEval, polyAsPolynomial, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial, Rat.coe_castHom]

theorem realEval_add (p q : Poly) (α : ℝ) :
    realEval (polyAdd p q) α = realEval p α+realEval q α := by
  simp only [realEval, polyAsPolynomial_add, Polynomial.eval₂_add]

theorem realEval_scale (p : Poly) (t : ℚ) (α : ℝ) :
    realEval (polyScale p t) α = (t:ℝ)*realEval p α := by
  simp only [realEval, polyAsPolynomial_scale, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Rat.coe_castHom]

theorem realEval_mul (p q : Poly) (α : ℝ) :
    realEval (polyMul p q) α = realEval p α*realEval q α := by
  simp only [realEval, polyAsPolynomial_mul, Polynomial.eval₂_mul]

theorem realEval_of_length_le (p : Poly) (α : ℝ) (N : ℕ) (hN : p.length ≤ N) :
    realEval p α = ∑ j ∈ range N, (coeff p j : ℝ)*α^j := by
  rw [realEval_eq_sum]
  apply Finset.sum_subset (Finset.range_mono hN)
  intro j _ hj
  rw [coeff_eq_zero_of_length_le p j (by simpa only [Finset.mem_range, not_lt] using hj)]
  simp

theorem realEval_const (c : ℚ) (α : ℝ) : realEval [c] α = (c:ℝ) := by
  simp [realEval_eq_sum, coeff]

theorem realEval_quadratic (c b a : ℚ) (α : ℝ) :
    realEval [c,b,a] α = (c:ℝ)+(b:ℝ)*α+(a:ℝ)*α^2 := by
  simp [realEval_eq_sum, coeff, Finset.sum_range_succ]

theorem realEval_zero (p : Poly) : realEval p 0 = (coeff p 0 : ℝ) := by
  rw [realEval_eq_sum]
  by_cases hp : 0 < p.length
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro j _ hj
      rw [zero_pow hj, mul_zero]
    · intro hz
      exact False.elim (hz (Finset.mem_range.mpr hp))
  · have hz : p = [] := List.length_eq_zero_iff.mp (by omega)
    subst p
    simp [coeff]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem odd_low_row_degree_bound : ∀ i : Fin 12, (rowPolynomial (lowIndex i)).length ≤ 7 := by
  decide +kernel

theorem odd_low_realEval_eq (i : Fin 12) (α : ℝ) :
    realEval (rowPolynomial (lowIndex i)) α = realRowPolynomial (lowIndex i) α :=
  realEval_of_length_le _ _ 7 (odd_low_row_degree_bound i)

theorem odd_low_realEval_positive (i : Fin 12) (α : ℝ) (hα : 0 ≤ α) (hα' : α ≤ 1/2) :
    (1/2:ℝ) ≤ realEval (rowPolynomial (lowIndex i)) α := by
  rw [odd_low_realEval_eq]
  exact odd_rows_positive_on_interval i α hα hα'

end Lemniscate.OddArithmetic
