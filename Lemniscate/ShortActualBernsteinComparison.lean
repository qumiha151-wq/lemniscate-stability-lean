import Lemniscate.ShortActualFormComparison
import Lemniscate.ShortActualReducedFormComparison

/-! One uniform error bound for all five genuine reduced Bernstein forms. -/
namespace Lemniscate
open Complex MeasureTheory CoarseArithmetic
open scoped ComplexConjugate
variable (T : ℝ) [Fact (0 < T)]

theorem short_actual_bernstein_form_error
    (q p : C(AddCircle T, ℂ))
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
    (j : Fin 5) (f : circleH4Domain T) (hf : f ∈ shortEvenDomain T) :
    ‖circleShiftedBernsteinPairing T (circleExactSymmetricCoefficient T q p hq hp ψ) j f f-
      circleShortBernsteinPairing T (q^2) ((2:ℂ) • (q*p)) (1-(3:ℂ) • (q^4)) j f f‖ ≤
        (9801/1280000:ℝ)*shortVNorm T f^2 := by
  exact short_reduced_bernstein_difference T _ _
    (short_actual_component_form_errors T q p hq hp he hqreal hpreal hs hc ho hr
      ψ hψnorm hψzero) j f hf

end Lemniscate
