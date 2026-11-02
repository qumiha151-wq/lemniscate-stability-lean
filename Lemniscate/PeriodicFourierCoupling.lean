import Lemniscate.InfiniteWeightedCoupling
import Lemniscate.PeriodicWeakFirst

/-! Fourier Parseval supplies the actual convergent pairing needed by the
weighted coupling bound. A coarse analytic quadratic bound avoids a separate
Bernstein computation for each coupling coefficient. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_fourier_pairing_hasSum (g y : CircleL2 T) :
    HasSum (fun n : ℤ => conj (fourierCoeff g n)*fourierCoeff y n) (inner ℂ g y) := by
  have hi (f : CircleL2 T) (n : ℤ) :
      inner ℂ (fourierBasis (T := T) n) f = fourierCoeff f n := by
    rw [← HilbertBasis.repr_apply_apply, fourierBasis_repr]
  have hg (n : ℤ) : inner ℂ g (fourierBasis (T := T) n) = conj (fourierCoeff g n) := by
    rw [← inner_conj_symm, hi]
  simpa only [hi, hg] using (fourierBasis (T := T)).hasSum_inner_mul_inner g y

theorem circle_supported_coupling_hasSum {ι : Type*} [Fintype ι]
    (g : ι → CircleL2 T) (x : ι → ℂ) (y : CircleL2 T) (S : Set ℤ)
    [DecidablePred (fun n => n ∈ S)]
    (hy : ∀ n ∉ S, fourierCoeff y n = 0) :
    HasSum (fun n : ℤ => ∑ i, conj (x i)*
      (if n ∈ S then conj (fourierCoeff (g i) n) else 0)*fourierCoeff y n)
      (∑ i, conj (x i)*inner ℂ (g i) y) := by
  classical
  apply hasSum_sum
  intro i _
  have h := (circle_fourier_pairing_hasSum T (g i) y).mul_left (conj (x i))
  have heq (n : ℤ) : conj (x i)*
      (if n ∈ S then conj (fourierCoeff (g i) n) else 0)*fourierCoeff y n =
      conj (x i)*(conj (fourierCoeff (g i) n)*fourierCoeff y n) := by
    by_cases hn : n ∈ S
    · simp only [if_pos hn, mul_assoc]
    · simp only [if_neg hn, hy n hn, mul_zero]
  simpa only [heq] using h

theorem circle_weighted_fourier_coupling {ι : Type*} [Fintype ι]
    (g : ι → CircleL2 T) (x : ι → ℂ) (y : CircleL2 T) (S : Set ℤ)
    [DecidablePred (fun n => n ∈ S)]
    (hy : ∀ n ∉ S, fourierCoeff y n = 0) (δ : ι → ℝ) (ω : ℤ → ℝ)
    (hδ : ∀ i, 0 < δ i) (hω : ∀ n, 0 < ω n)
    (hC : Summable (fun n : ℤ => ∑ i,
      ‖if n ∈ S then conj (fourierCoeff (g i) n) else 0‖^2/(δ i*ω n)))
    (hW : Summable (fun n : ℤ => ω n*‖fourierCoeff y n‖^2)) :
    ‖∑ i, conj (x i)*inner ℂ (g i) y‖^2 ≤
      (∑' n : ℤ, ∑ i, ‖if n ∈ S then conj (fourierCoeff (g i) n) else 0‖^2/(δ i*ω n))*
        (∑ i, δ i*‖x i‖^2)*(∑' n : ℤ, ω n*‖fourierCoeff y n‖^2) := by
  classical
  exact infinite_weighted_coupling _ δ ω x (fun n => fourierCoeff y n) hδ hω hC hW _
    (circle_supported_coupling_hasSum T g x y S hy)

theorem quadratic_complex_norm_sq_le_two (a b c : ℂ) (α : ℝ) (hα : |α| ≤ 1/2) :
    ‖a+(α:ℂ)*b+(α:ℂ)^2*c‖^2 ≤ 2*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have hα₂ : |α|^2 ≤ (1/4:ℝ) := by
    have h := pow_le_pow_left₀ (abs_nonneg α) hα 2
    norm_num at h
    simpa only [sq_abs] using h
  have hb : ‖(α:ℂ)*b‖ ≤ (1/2:ℝ)*‖b‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hα (norm_nonneg b)
  have hc : ‖(α:ℂ)^2*c‖ ≤ (1/4:ℝ)*‖c‖ := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hα₂ (norm_nonneg c)
  have hsum : ‖a+(α:ℂ)*b+(α:ℂ)^2*c‖ ≤ ‖a‖+(1/2:ℝ)*‖b‖+(1/4:ℝ)*‖c‖ := by
    calc
      _ ≤ ‖a‖+‖(α:ℂ)*b‖+‖(α:ℂ)^2*c‖ := by
        linarith only [norm_add_le (a+(α:ℂ)*b) ((α:ℂ)^2*c), norm_add_le a ((α:ℂ)*b)]
      _ ≤ _ := by linarith only [hb, hc]
  have hpoly : (‖a‖+(1/2:ℝ)*‖b‖+(1/4:ℝ)*‖c‖)^2 ≤ 2*(‖a‖^2+‖b‖^2+‖c‖^2) := by
    nlinarith only [sq_nonneg (‖a‖-‖b‖), sq_nonneg (‖a‖-‖c‖), sq_nonneg (‖b‖-‖c‖),
      sq_nonneg ‖a‖, sq_nonneg ‖b‖, sq_nonneg ‖c‖]
  exact (pow_le_pow_left₀ (norm_nonneg _) hsum 2).trans hpoly

end Lemniscate
