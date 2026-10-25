import Lemniscate.PeriodicOddCoefficients
import Lemniscate.PeriodicOddPolynomials

/-! Odd Fourier polynomials converge to an actual odd-sector H2 function
simultaneously with both of its weak derivatives. -/
namespace Lemniscate
open Complex MeasureTheory Filter
open scoped Topology

variable (T : ℝ) [Fact (0 < T)]

theorem circle_odd_polynomial_tendsto (f : CircleL2 T) (hf : InCircleOddSector T f) :
    Tendsto (fun I : Finset ℤ => circleContinuousL2 T
      (circleOddPolynomial T I (fun i => fourierCoeff f (2*i+1)) 0)) atTop (𝓝 f) := by
  have hs : Tendsto (fun I : Finset ℤ =>
      ∑ i ∈ I, fourierCoeff f (2*i+1) • fourierBasis (T := T) (2*i+1))
      atTop (𝓝 f) := circle_odd_fourier_hasSum T f hf
  simpa only [circle_odd_polynomial_l2, pow_zero, mul_one] using hs

theorem circle_odd_polynomial_first_tendsto (f f₁ : CircleL2 T)
    (hf : InCircleOddSector T f) (hff₁ : HasWeakCircleDeriv T f f₁) :
    Tendsto (fun I : Finset ℤ => circleContinuousL2 T
      (circleOddPolynomial T I (fun i => fourierCoeff f (2*i+1)) 1)) atTop (𝓝 f₁) := by
  have hs : Tendsto (fun I : Finset ℤ =>
      ∑ i ∈ I, fourierCoeff f₁ (2*i+1) • fourierBasis (T := T) (2*i+1))
      atTop (𝓝 f₁) := circle_odd_fourier_hasSum T f₁ (circle_odd_sector_weak_deriv T f f₁ hf hff₁)
  simpa only [circle_odd_polynomial_l2, pow_one,
    fourier_of_weak_circle_deriv T f f₁ hff₁, mul_comm] using hs

theorem circle_odd_polynomial_second_tendsto (f f₁ f₂ : CircleL2 T)
    (hf : InCircleOddSector T f) (hff₁ : HasWeakCircleDeriv T f f₁)
    (hf₁f₂ : HasWeakCircleDeriv T f₁ f₂) :
    Tendsto (fun I : Finset ℤ => circleContinuousL2 T
      (circleOddPolynomial T I (fun i => fourierCoeff f (2*i+1)) 2)) atTop (𝓝 f₂) := by
  have hs : Tendsto (fun I : Finset ℤ =>
      ∑ i ∈ I, fourierCoeff f₂ (2*i+1) • fourierBasis (T := T) (2*i+1))
      atTop (𝓝 f₂) := circle_odd_fourier_hasSum T f₂ (circle_odd_sector_weak_deriv T f₁ f₂
    (circle_odd_sector_weak_deriv T f f₁ hf hff₁) hf₁f₂)
  have hc (n : ℤ) : fourierCoeff f₂ n = fourierCoeff f n*(circleFrequencyFactor T n)^2 := by
    rw [fourier_of_weak_circle_deriv T f₁ f₂ hf₁f₂,
      fourier_of_weak_circle_deriv T f f₁ hff₁]
    ring
  simpa only [circle_odd_polynomial_l2, hc] using hs

end Lemniscate
