import Lemniscate.PeriodicFiniteCouplingPolynomial
import Lemniscate.PeriodicHighFourierDuality

/-! Reduce the actual coupling estimate to three parameter-independent
test-function estimates. The quantitative test estimate is an explicit premise
here and must be proved from the profile bounds before the even-sector theorem. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem circle_finite_coupling_of_test_estimate (h h₁ h₂ : C(AddCircle T, ℂ))
    (hh : HasCircleDeriv T h h₁) (hh₁ : HasCircleDeriv T h₁ h₂)
    (hreal : ∀ x, conj (h x) = h x) (h₁real : ∀ x, conj (h₁ x) = h₁ x)
    (h₂real : ∀ x, conj (h₂ x) = h₂ x) (α : ℝ) (hα : |α| ≤ 1/2)
    (v : Fin 31 → ℂ) (y : circleH4Domain T) (S : Set ℤ)
    [DecidablePred (fun n => n ∈ S)]
    (hS : ∀ n ∈ S, 32 ≤ |(n:ℝ)|)
    (hy : ∀ n ∉ S, fourierCoeff (y:CircleL2 T) n = 0) (E : ℝ)
    (ht : (∑ j : Fin 3, ∑' n : ℤ, if n ∈ S then
      ‖fourierCoeff (circleFiniteCouplingTestCoefficient T h h₁ h₂ j v) n‖^2/(n:ℝ)^4 else 0) ≤ E/8) :
    ‖circleFiniteBlochPairing T h h₁ h₂ α (circleEvenHeadH4 T v) y‖^2 ≤
      (E/4)*(∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (y:CircleL2 T) n‖^2) := by
  classical
  let C (j : Fin 3) : ℝ := ∑' n : ℤ, if n ∈ S then
    ‖fourierCoeff (circleFiniteCouplingTestCoefficient T h h₁ h₂ j v) n‖^2/(n:ℝ)^4 else 0
  let W : ℝ := ∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (y:CircleL2 T) n‖^2
  have ht' : C 0+C 1+C 2 ≤ E/8 := by
    simpa [C, Fin.sum_univ_succ, add_assoc] using ht
  have hw : 0 ≤ W := tsum_nonneg (fun n => mul_nonneg (by positivity) (sq_nonneg _))
  have hb (j : Fin 3) :
      ‖inner ℂ (circleFiniteCouplingTestCoefficient T h h₁ h₂ j v) (y:CircleL2 T)‖^2 ≤ C j*W :=
    circle_high_fourier_duality T _ y S hS hy
  have hy0 (n : ℤ) (hn : |(n:ℝ)| < 32) : fourierCoeff (y:CircleL2 T) n = 0 :=
    hy n (fun hs => not_lt_of_ge (hS n hs) hn)
  rw [circle_finite_coupling_polynomial T h h₁ h₂ hh hh₁ hreal h₁real h₂real α v y hy0]
  simp only [inner_add_left, inner_smul_left, map_pow, Complex.conj_ofReal]
  have hq := quadratic_complex_norm_sq_le_two
    (inner ℂ (circleFiniteCouplingTestCoefficient T h h₁ h₂ 0 v) (y:CircleL2 T))
    (inner ℂ (circleFiniteCouplingTestCoefficient T h h₁ h₂ 1 v) (y:CircleL2 T))
    (inner ℂ (circleFiniteCouplingTestCoefficient T h h₁ h₂ 2 v) (y:CircleL2 T)) α hα
  have hsum := add_le_add (add_le_add (hb 0) (hb 1)) (hb 2)
  have hcw := mul_le_mul_of_nonneg_right ht' hw
  change _ ≤ (E/4)*W
  nlinarith only [hq, hsum, hcw]

end Lemniscate
