import Lemniscate.ShortExactPolynomialCoercivity
import Lemniscate.ShortH4Density
import Lemniscate.ShortBernsteinForms

/-! Exact coercivity follows from the new full-frequency Schur estimate,
the seven-mode vector errors, H4 Fourier approximation, and Bernstein
positivity. No old finite Bloch certificate is used. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem paper_exact_reduced_even_coercivity (q p : C(AddCircle T, ℂ))
    (hq : HasCircleDeriv T q p) (hp : HasCircleDeriv T p (-(q^3)))
    (he : ∀ x, 2*(p x)^2+(q x)^4 = 1)
    (hqreal : ∀ x, conj (q x) = q x) (hpreal : ∀ x, conj (p x) = p x)
    (hs : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (-n) =
      fourierCoeff (q^2 : C(AddCircle T, ℂ)) n)
    (hc : ∀ j : ℕ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*(j:ℤ)) =
      (fourierCoefficient lemniscateFrequencySquared nome j:ℂ))
    (ho : ∀ n : ℤ, fourierCoeff (q^2 : C(AddCircle T, ℂ)) (2*n+1) = 0)
    (hr : (2*Real.pi/T)^2 = lemniscateFrequencySquared)
    (ψ : circleH4Domain T)
    (hψnorm : inner ℂ (ψ:CircleL2 T) (circleUnitRotation T q p) = 1)
    (hψzero : circleH4FormalAdjoint T (q^2) ((2:ℂ) • (q*p)) ψ = 0)
    (α : ℝ) (hα0 : 0 ≤ α) (hαhalf : α ≤ 1/2)
    (f : circleH4Domain T)
    (hf : ∀ n : ℤ, Odd n → fourierCoeff (f:CircleL2 T) n = 0) :
    (circleExactReducedBlochPairing T q p hq hp ψ α f f).re ≤ -(1/2:ℝ)*‖(f:CircleL2 T)‖^2 := by
  apply circle_reduced_bound_of_bernstein T
    (circleExactSymmetricCoefficient T q p hq hp ψ) f _ α hα0 hαhalf
  intro j
  exact short_exact_bernstein_nonpositive_of_polynomials T q p hq hp ψ j
    (short_exact_polynomial_bernstein_nonpositive T q p hq hp he hqreal hpreal
      hs hc ho hr ψ hψnorm hψzero j) f hf

end Lemniscate
