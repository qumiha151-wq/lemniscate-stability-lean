import Lemniscate.PeriodicBlochGarding

/-! A coarse analytic high-frequency bound, using only Parseval and the
shifted Garding estimate, for the complete high-frequency Fourier subspace. -/
namespace Lemniscate
open Complex MeasureTheory
open scoped ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

theorem circle_bloch_second_fourier_sq (α : ℝ) (f : circleH4Domain T) (n : ℤ) :
    ‖fourierCoeff (circleShiftedSecond T ((α:ℂ)*circleFrequencyFactor T 1) f) n‖^2 =
      (2*Real.pi/T)^4*((n:ℝ)+α)^4*‖fourierCoeff (f : CircleL2 T) n‖^2 := by
  let z := (α:ℂ)*circleFrequencyFactor T 1
  rcases circle_h4_shifted_derivative_chain T z f with ⟨hf, hf₁, _, _⟩
  rw [circle_shifted_deriv_fourier T z _ _ hf₁ n,
    circle_shifted_deriv_fourier T z _ _ hf n]
  have hm : circleFrequencyFactor T n+z =
      (((2*Real.pi/T)*((n:ℝ)+α):ℝ):ℂ)*I := by
    simp only [circleFrequencyFactor, z]
    push_cast
    ring
  rw [hm]
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private theorem high_frequency_garding_symbol (r n α : ℝ)
    (hr : (7/10:ℝ) ≤ r) (hn : 32 ≤ |n|) (hα : |α| ≤ 1/2) :
    -2*r^2*(n+α)^4+(1719/8:ℝ) ≤ -(1/2:ℝ)*n^4 := by
  have hshift : (15/16:ℝ)*|n| ≤ |n+α| := by
    have htri : |n| ≤ |n+α|+|α| := by
      simpa only [add_sub_cancel_right] using abs_sub (n+α) α
    linarith
  have hshift4 := pow_le_pow_left₀ (by positivity : 0 ≤ (15/16:ℝ)*|n|) hshift 4
  have hr2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/10) hr 2
  have hn4 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 32) hn 4
  have habs (x : ℝ) : |x|^4 = x^4 := by
    calc
      _ = (|x|^2)^2 := by ring
      _ = (x^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  rw [mul_pow, habs, habs] at hshift4
  rw [habs] at hn4
  have hprod := mul_le_mul hr2 hshift4
    (by positivity : 0 ≤ (15/16:ℝ)^4*n^4) (sq_nonneg r)
  norm_num at hn4 hprod
  nlinarith only [hn4, hprod]

theorem circle_fourier_fourth_weight_summable (f : circleH4Domain T) :
    Summable (fun n : ℤ => (n:ℝ)^4*‖fourierCoeff (f : CircleL2 T) n‖^2) := by
  let g := circleShiftedSecond T ((0:ℂ)*circleFrequencyFactor T 1) f
  have hκ : 2*Real.pi/T ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (ne_of_gt (Fact.out : 0 < T))
  have hs := (circle_fourier_square_summable T g).mul_left ((2*Real.pi/T)^4)⁻¹
  apply hs.congr
  intro n
  dsimp only [g]
  have hzero := circle_bloch_second_fourier_sq T 0 f n
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hzero ⊢
  rw [hzero]
  field_simp [hκ, ne_of_gt (Fact.out : 0 < T)]

theorem paper_bloch_high_frequency_energy (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hr : (7/10:ℝ) ≤ (2*Real.pi/T)^2) (α : ℝ) (hα : |α| ≤ 1/2)
    (f : circleH4Domain T)
    (hf : ∀ n : ℤ, |(n:ℝ)| < 32 → fourierCoeff (f : CircleL2 T) n = 0) :
    (inner ℂ (f : CircleL2 T)
      (circleBlochOperator T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f)).re ≤
        -(1/2:ℝ)*(∑' n : ℤ, (n:ℝ)^4*‖fourierCoeff (f : CircleL2 T) n‖^2) := by
  let g := circleShiftedSecond T ((α:ℂ)*circleFrequencyFactor T 1) f
  have hcoeff (n : ℤ) :
      -2*‖fourierCoeff g n‖^2+(1719/8:ℝ)*‖fourierCoeff (f : CircleL2 T) n‖^2 ≤
        -(1/2:ℝ)*((n:ℝ)^4*‖fourierCoeff (f : CircleL2 T) n‖^2) := by
    dsimp only [g]
    rw [circle_bloch_second_fourier_sq]
    by_cases hn : 32 ≤ |(n:ℝ)|
    · have h := mul_le_mul_of_nonneg_right
        (high_frequency_garding_symbol ((2*Real.pi/T)^2) (n:ℝ) α hr hn hα)
        (sq_nonneg ‖fourierCoeff (f : CircleL2 T) n‖)
      nlinarith only [h]
    · rw [hf n (lt_of_not_ge hn), norm_zero]
      norm_num
  have hgs := (circle_fourier_square_summable T g).mul_left (-2:ℝ)
  have hfs := (circle_fourier_square_summable T (f : CircleL2 T)).mul_left (1719/8:ℝ)
  have hrs := (circle_fourier_fourth_weight_summable T f).mul_left (-(1/2:ℝ))
  have hsum := (hgs.add hfs).tsum_le_tsum hcoeff hrs
  rw [hgs.tsum_add hfs, tsum_mul_left, tsum_mul_left, tsum_mul_left,
    ← circle_norm_sq_fourier, ← circle_norm_sq_fourier] at hsum
  exact (paper_bloch_operator_garding T q p hq hp he hqreal hpreal α f).trans hsum

end Lemniscate
