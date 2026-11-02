import Lemniscate.PeriodicFiniteBlochPolynomial

/-! A quartic Bernstein convex combination preserves a common quadratic-form
upper bound. No interval data or spectral premise enters this lemma. -/
namespace Lemniscate
open Complex Matrix

theorem head_pair_sum_right {ι : Type*} [Fintype ι]
    (v : Fin 31 → ℂ) (w : ι → Fin 31 → ℂ) :
    headPair v (∑ k, w k) = ∑ k, headPair v (w k) := by
  simp only [headPair, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem head_pair_bernstein_upper_bound (B : Fin 5 → Matrix (Fin 31) (Fin 31) ℂ)
    (v : Fin 31 → ℂ) (α E : ℝ) (ha : 0 ≤ α) (ha' : α ≤ 1/2)
    (hB : ∀ k, (headPair v (B k *ᵥ v)).re ≤ E) :
    (headPair v ((∑ k : Fin 5, (bernsteinBasis 4 k.val α:ℂ) • B k) *ᵥ v)).re ≤ E := by
  have hs : ∑ k : Fin 5, bernsteinBasis 4 k.val α = 1 := by
    have h := bernsteinBasis_sum 4 α
    rw [← Fin.sum_univ_eq_sum_range] at h
    exact h
  rw [sum_mulVec, head_pair_sum_right]
  simp only [smul_mulVec, head_pair_smul_right]
  change Complex.reCLM (∑ k : Fin 5,
    (bernsteinBasis 4 k.val α:ℂ)*headPair v (B k *ᵥ v)) ≤ E
  rw [map_sum]
  change (∑ k : Fin 5, ((bernsteinBasis 4 k.val α:ℂ)*headPair v (B k *ᵥ v)).re) ≤ E
  simp only [Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  calc
    _ ≤ ∑ k : Fin 5, bernsteinBasis 4 k.val α*E := Finset.sum_le_sum (fun k _ =>
      mul_le_mul_of_nonneg_left (hB k) (bernsteinBasis_nonneg 4 k.val α ha ha'))
    _ = E := by rw [← Finset.sum_mul, hs, one_mul]

end Lemniscate
