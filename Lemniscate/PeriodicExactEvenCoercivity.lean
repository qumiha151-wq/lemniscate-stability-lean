import Lemniscate.PeriodicExactFormComparison
import Lemniscate.PeriodicProfileCoefficientBounds
import Lemniscate.PeriodicEvenCoercivity

/-! Transfer the whole even-sector energy estimate to the exact reduced
form. Identification with the scaled centered operator is a separate step. -/
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
  rcases circle_profile_coefficient_norm_bounds T q p he hqreal hpreal with ⟨hh,hh₁,hh₂⟩
  have hα : |α| ≤ 1 := abs_le.mpr ⟨by linarith only [hα0],by linarith only [hαhalf]⟩
  have herror := paper_exact_finite_reduced_form_difference T q p hq hp he hqreal hpreal hs hc ho hr
    ψ hψnorm hψzero hh hh₁ hh₂ (paper_frequency_le_one T hr) α hα f
  have hfinite := paper_finite_even_coercivity T q p hq hp he hqreal hpreal hs hc hr α hα0 hαhalf f hf
  have hre := Complex.re_le_norm (circleExactReducedBlochPairing T q p hq hp ψ α f f-
    circleFiniteBlochPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f f)
  simp only [Complex.sub_re] at hre
  change ‖circleExactReducedBlochPairing T q p hq hp ψ α f f-
    circleFiniteBlochPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) α f f‖ ≤
      (1/100:ℝ)*‖(f:CircleL2 T)‖^2 at herror
  nlinarith only [herror,hfinite,hre,sq_nonneg ‖(f:CircleL2 T)‖]

end Lemniscate
